----------------------- MODULE ViewStampedReplication -----------------------
\* TODO P4 - View change without flooding of start_view_change message.

\* Challenges - running with view change is tough, have to limit the model till a maximum view number.

\* TODO - VR with flexible quorums?
(* Think of this - What if a process sends start_view_change immediately after a do_view_change? Can this be solved?
   For this issue, does PBFT have a solution? Because a byzantine node can do this always.
*)

EXTENDS Integers, Sequences, FiniteSets

CONSTANT
    NumProcesses,   \* The set of processes
    ClientCommands, \* The set of client commands. For now each client has just one command
    MaxViewNum,
    MaxFailures

VARIABLES
    messages,
    (*
        A function mapping process number to process record -
            [
                view_num |-> 0,
                log |-> <<>>,
                commit_num |-> 0,
                status |-> "normal" / "view_change" / "do_view_change_sent"/ "recovering",
                last_active_view_num |-> 0
            ]
    *)
    processState

(* Utility operators *)
\* TODO - Fix Cardinality
PossibleLogSeqences(S) == {possible_seq \in UNION {[1..n -> S] : n \in 0..Cardinality({2, 3})}: (\A a, b \in 1..Len(possible_seq): (a = b \/ possible_seq[a] # possible_seq[b]))}

\* isLeader return True if p thinks it is the leader.
isLeader(p) == processState[p].view_num % NumProcesses = p

sendMsgs(msgs) == messages' = messages \cup msgs

(* Normal case operation *)
sendPrepares(p) == /\ \E cmd \in ClientCommands: (
                      /\ (
                          LET set[i \in 0..Len(processState[p].log)] ==
                                IF i = 0 THEN {}
                                ELSE set[i-1] \cup {processState[p].log[i]}
                          IN ~ (cmd \in set[Len(processState[p].log)]))
                      /\ processState' = [processState EXCEPT ![p].log = Append(processState[p].log, cmd)]
                      /\ sendMsgs(
                                  {
                                      [type |-> "prepare",
                                       to |-> listener,
                                       from |-> p,
                                       cmd |-> cmd,
                                       view_num |-> processState[p].view_num,
                                       commit_num |-> processState[p].commit_num,
                                       log_num |-> Len(processState[p].log)+1] : listener \in 0..NumProcesses-1 \ {p}
                                  }
                               )
                    )

sendCommits(p) == /\ sendMsgs(
                        {
                            [type |-> "commit",
                             to |-> listener,
                             from |-> p,
                             view_num |-> processState[p].view_num,
                             commit_num |-> processState[p].commit_num]: listener \in 0..NumProcesses-1 \ {p}
                        }
                     )

\* Check if there are atleast NumProcesses/2 PREPAREOKs. Note that there is an implicit self PREPAREOK which completes the majority.
majorityPREPAREOKs(p, log_num) == LET mset == {
                                        msg \in messages: /\ msg.type = "prepareOk"
                                                          /\ msg.view_num = processState[p].view_num
                                                          /\ msg.log_num = log_num
                                                          /\ msg.to = p
                                    }
                                  IN /\ Cardinality(mset) >= NumProcesses \div 2

\* In case a higher view number is seen execute some state transfer and catch up. This is needed
\* in acceptRequest as well. To handle for every case, add a transition in VRNext itself in case
\* the process sees a message for itself with a higher view number. Handle this later.

acceptPrepare(p) == /\ \E msg \in messages:
                        /\ msg.type = "prepare"
                        /\ msg.to = p
                        /\ processState[p].view_num = msg.view_num
                        /\ Len(processState[p].log) = msg.log_num - 1
                        /\ processState' = [processState EXCEPT ![p].log = Append(processState[p].log, msg.cmd),
                                                                ![p].commit_num = msg.commit_num]
                        /\ sendMsgs({
                                        [type |-> "prepareOk",
                                         to |-> processState[p].view_num % NumProcesses,
                                         from |-> p,
                                         view_num |-> processState[p].view_num,
                                         log_num |-> Len(processState[p].log)+1]
                                    })

acceptCommit(p) == /\ \E msg \in messages:
                        /\ msg.type = "commit"
                        /\ msg.to = p
                        /\ processState[p].view_num = msg.view_num
                        /\ Len(processState[p].log) >= msg.commit_num
                        /\ processState[p].commit_num < msg.commit_num
                        /\ processState' = [processState EXCEPT ![p].commit_num = msg.commit_num]

(* View change steps *)
sendStartViewChange(p, new_view_num) == 
                      /\ new_view_num > processState[p].view_num
                      /\ processState' = [processState EXCEPT ![p].status = "view_change",
                                                              ![p].view_num = new_view_num]
                      /\ sendMsgs({
                            [type |-> "start_view_change",
                             to |-> listener,
                             from |-> p,
                             view_num |-> new_view_num] : listener \in 0..NumProcesses-1 \ {p}
                        })

sendDoViewChange(p, newLeader) == /\ sendMsgs({
                                        [
                                            type |-> "do_view_change",
                                            from |-> p,
                                            to |-> newLeader,
                                            view_num |-> processState[p].view_num,
                                            log |-> processState[p].log,
                                            commit_num |-> processState[p].commit_num,
                                            last_active_view_num |-> processState[p].last_active_view_num
                                        ]})

updateBasedOnStartView(p, msg) == /\ processState' = [processState EXCEPT ![p].status = "normal",
                                                                          ![p].commit_num = msg.commit_num,
                                                                          ![p].log = msg.log,
                                                                          ![p].last_active_view_num = msg.view_num,
                                                                          ![p].view_num = msg.view_num]

viewChangeTransitions(p) == 
                          \/ (
                                /\ ~(processState[p].status = "view_change")
                                /\ (
                                        \* Timer triggered view change. Can't be done by node which thinks its the leader.
                                        /\ ~isLeader(p)
                                        /\ processState[p].view_num+1 <= MaxViewNum
                                        /\ sendStartViewChange(p, processState[p].view_num+1)
                                   )
                             )
                          \/ (
                                \* Wait for majority to say view_change and then perform do_view_change
                                /\ processState[p].status = "view_change"
                                /\ LET mset == {
                                            msg \in messages: /\ msg.type = "start_view_change"
                                                              /\ msg.view_num = processState[p].view_num
                                                              /\ msg.to = p
                                        }
                                   IN /\ Cardinality(mset) >= NumProcesses \div 2
                                /\ sendDoViewChange(p, processState[p].view_num % NumProcesses)
                                /\ processState' = [processState EXCEPT ![p].status = "do_view_change_sent"]
                             )
                          \/ (
                                \* Remove? - In view_change status, but got view_change with higher number.
                                /\ \* Got larger start_view_change msg from another node.
                                   (\E msg \in messages: msg.type = "start_view_change" /\ msg.view_num > processState[p].view_num
                                      /\ sendStartViewChange(p, msg.view_num))
                             )
                          \/ (
                                \* In case a start_view msg is received
                                /\ (
                                      \/ (
                                          /\ \E msg \in messages: msg.type = "start_view" /\ msg.view_num > processState[p].view_num
                                              /\ updateBasedOnStartView(p, msg)
                                         )
                                      \/ (
                                          \* TODO - Find the invariant to check the case where "normal" wasn't checked when updating with start_view
                                          \* message of same view_num
                                          /\ ~(processState[p].status = "normal")
                                          /\ \E msg \in messages: msg.type = "start_view" /\ msg.view_num = processState[p].view_num
                                              /\ updateBasedOnStartView(p, msg)
                                         )
                                   )
                                /\ UNCHANGED <<messages>>
                             )

\* There is no "to" field in start_view as it is for all replicas.
sendStartView(p, v, maxLogMsg) == sendMsgs(
                                {
                                    [type |-> "start_view",
                                     from |-> p,
                                     log |-> maxLogMsg.log,
                                     view_num |-> v,
                                     commit_num |-> maxLogMsg.commit_num]
                                }
                             )

recvMajortiyDoViewChange(p, v) == LET
                                        mset == {
                                            msg \in messages: /\ msg.type = "do_view_change"
                                                              /\ msg.view_num = v
                                                              /\ msg.to = p
                                        }
                                        maxLogMsg == IF mset = {} THEN -1
                                            ELSE CHOOSE msg \in mset : \A msg2 \in mset :
                                                (\/ (msg.last_active_view_num > msg2.last_active_view_num)
                                                 \/ (/\ msg.last_active_view_num = msg2.last_active_view_num /\ Len(msg.log) \geq Len(msg2.log)))
                                  IN /\ Cardinality(mset) >= ((NumProcesses \div 2) + 1)
                                     /\ processState' = [processState EXCEPT ![p].view_num = v,
                                                                             ![p].status = "normal",
                                                                             ![p].log = maxLogMsg.log,
                                                                             ![p].commit_num = maxLogMsg.commit_num,
                                                                             ![p].last_active_view_num = v]
                                     /\ sendStartView(p, v, maxLogMsg)

NormalCaseOperation(p) ==  \/
                              \* A process, which thinks it is the leader, sends PREPARE messages.
                              /\ isLeader(p)
                              /\ sendPrepares(p)
                              /\ UNCHANGED <<>>
        
                           \/
                              \* A process, which thinks it is the leader, sends COMMIT messages.
                              /\ isLeader(p)
                              /\ sendCommits(p)
                              /\ UNCHANGED <<processState>>
        
                           \/ \* A process, which thinks it is the leader, advances its commit number if majority PREPAREOKs have been received.
                              \* Note that a leader can advance commit numbers non-sequentially.
                              /\ isLeader(p)
                              /\ \E log_num \in (processState[p].commit_num+1)..Len(processState[p].log):
                                   /\ majorityPREPAREOKs(p, log_num)
                                   /\ processState' = [processState EXCEPT ![p].commit_num = log_num]
                              /\ UNCHANGED <<messages>>
        
                           \/ \* Normal case operation of a replica node.
                              /\ ~isLeader(p)
                              /\
                                 \/
                                    /\ acceptPrepare(p)
                                    /\ UNCHANGED <<>>
                                 \/
                                    /\ acceptCommit(p)
                                    /\ UNCHANGED <<messages>>

                           \/ \* Respond to RECOVERY messages.
                              /\ \E msg \in messages:
                                   /\ msg.type = "RECOVERY"
                                   /\
                                      \/ 
                                         /\ isLeader(p)
                                         /\ sendMsgs(
                                            {
                                              [type |-> "RECOVERYRESPONSE",
                                               from |-> p,
                                               to |-> msg.from,
                                               view_num |-> processState[p].view_num,
                                               commit_num |-> processState[p].commit_num,
                                               log |-> processState[p].log,
                                               nonce |-> msg.nonce]
                                            })
                                       \/
                                          /\ ~isLeader(p)
                                          /\ sendMsgs(
                                             {
                                               [type |-> "RECOVERYRESPONSE",
                                                from |-> p,
                                                to |-> msg.from,
                                                view_num |-> processState[p].view_num,
                                                nonce |-> msg.nonce]
                                             })
                                   /\ UNCHANGED <<processState>>

\* When a node fails, it loses all data and goes into recovering status.
FailNode(p) == 
               /\ processState' = [processState EXCEPT ![p].commit_num = 0,
                                                       ![p].view_num = 0,
                                                       ![p].last_active_view_num = 0,
                                                       ![p].log = <<>>,
                                                       ![p].status = "recovering"]
               /\ sendMsgs(
                                {
                                    [type |-> "RECOVERY",
                                     from |-> p,
                                     nonce |-> processState[p].nonce]
                                }
                             )

\* There are a few ways to handle nonce, this spec follows the first one -
\* 1. Store it on disk and increment it just before a node marks itself "normal".
\* 2. Store it on disk and increment it whenever a node restarts to come into "recovering" status. But this has higher message
\*    complexity considering this scneario - if an already recovering node restarts, it will ignore the RECOVERYRESPONSE
\*    messages from all other nodes since they are from an ealier nonce, even though using those responses would have not violateed
\*    safety. This will require another set of RECOVERYRESPONSE messages.
\* 3. Use a clock value to generate nonce

Recover(p) == LET
                    \* There might be more than one RECOVERYRESPONSE messages from the same process.
                    mset == {
                        msg \in messages: /\ msg.type = "RECOVERYRESPONSE"
                                          /\ msg.nonce = processState[p].nonce
                                          /\ msg.to = p
                    }
                    sender_set == {p_id \in 0..NumProcesses-1: (\E msg \in mset: msg.from = p_id)}
                    maxViewMsg == IF mset = {} THEN <<>>
                        ELSE CHOOSE msg \in mset : \A msg2 \in mset :
                          \/ (msg.view_num >= msg2.view_num)
                    maxViewNum == IF maxViewMsg = <<>> THEN -1
                                  ELSE maxViewMsg.view_num
              IN 
                 /\ processState[p].nonce < MaxFailures
                 /\ Cardinality(sender_set) >= ((NumProcesses \div 2) + 1)
                 \* Very important - 
                 \* Step through all behaviours where process p chooses any of the RECOVERYRESPONSEs from the leader of maxViewNum.
                 /\ \E msg \in mset:
                      /\ msg.from = maxViewNum % NumProcesses
                      /\ msg.view_num = maxViewNum \* This is important, if this check is not included, an older RECOVERYRESPONSE from the leader might be used. TODO - Bring in an invariant
                      /\ processState' = [processState EXCEPT ![p].view_num = maxViewNum,
                                                              ![p].status = "normal",
                                                              ![p].log = msg.log,
                                                              ![p].commit_num = msg.commit_num,
                                                              ![p].last_active_view_num = maxViewNum,
                                                              \* TODO - Consider the case where the process increments
                                                              \* the nonce and then fails again. Right now, switching
                                                              \* to normal and nonce incrementing is atomic, but
                                                              \* it should not be so.
                                                              ![p].nonce = processState[p].nonce + 1]

VRInit == /\ messages = {}
          /\ processState =
                    [p \in 0..NumProcesses-1 |-> [
                                                    view_num |-> 0,
                                                    log |-> <<>>,
                                                    commit_num |-> 0,
                                                    status |-> "normal", \* normal, view_change, do_view_change_sent, recovering
                                                    last_active_view_num |-> 0,
                                                    nonce |-> 0
                                                  ]
                    ]

VRNext ==
          \/ \* Normal case operation. Executed only when status of process is normal
             /\ \E p \in 0..NumProcesses-1:
                  /\ processState[p].status = "normal"
                  /\ NormalCaseOperation(p)

          \/ \* View change transitions. All except "recovering" status nodes can take this step.
             /\ \E p \in 0..NumProcesses-1:
                  /\ processState[p].status # "recovering"
                  /\ viewChangeTransitions(p)

          \/ \E p \in 0..NumProcesses-1:
               /\ processState[p].status # "recovering"
               /\ \E v \in 0..MaxViewNum:
                    (
                        \* ~isLeader(p) is not kept here because it might happen that a leader again becomes the next leader.
                        \* TODO - What safety check would catch such an error?
                        /\ (
                            \/ v > processState[p].view_num \* TODO - Think of coming up with an invariant which is false in case we just have one condition with v >= processState[p].view_num
                            \/ (v = processState[p].view_num /\ ~(processState[p].status = "normal")) 
                           )
                        /\ v % NumProcesses = p
                        /\ recvMajortiyDoViewChange(p, v)
                    )

          \/ \* Fail a process. It goes to status "recovering"
             LET
                failed_processes == {p \in 0..NumProcesses-1: processState[p].status = "recovering"}
             IN
                /\ Cardinality(failed_processes) < ((NumProcesses-1) \div 2)
                /\ \E p \in (0..NumProcesses-1 \ failed_processes):
                     /\ FailNode(p)
                /\ UNCHANGED <<>>
          \/ \* Recover a recovering process, if the RECOVERYRESPONSEs have been received.
             \E p \in {p \in 0..NumProcesses-1: processState[p].status = "recovering"}:
                /\ Recover(p)
                /\ UNCHANGED <<messages>>

(* Invariants *)
VRTypeOk == /\ processState \in [0..NumProcesses-1 -> [
                view_num : 0..MaxViewNum,
                commit_num: 0..Cardinality(ClientCommands),
                status: {"normal", "view_change", "do_view_change_sent", "recovering"},
                last_active_view_num: 0..MaxViewNum,
                log: PossibleLogSeqences(ClientCommands),
                nonce: 0..MaxFailures]]

(* Invariant - for any two processes, log till lesser commit number is the same (Prefix property) *)

\* True if sequence a is a prefix of b
PrefixOf(a, b) == /\ Len(a) <= Len(b)
                  /\ \A i \in 1..Len(a): a[i] = b[i]

PrefixLogConsistency == \A a, b \in 0..NumProcesses-1:
                            \/ a = b
                            \/ PrefixOf(
                                SubSeq(processState[a].log, 1, processState[a].commit_num),
                                SubSeq(processState[b].log, 1, processState[b].commit_num))
                            \/ PrefixOf(
                                SubSeq(processState[b].log, 1, processState[b].commit_num),
                                SubSeq(processState[a].log, 1, processState[a].commit_num))

(* Invariant - process with higher view_num in normal state
   has larger log than last committed log of process in lower
   view_num *)
ViewNumCommitNumInv == \A a, b \in 0..NumProcesses-1:
                            \/ a = b
                            \/ IF /\ processState[a].status = "normal"
                                  /\ processState[b].status = "normal"
                                  /\ processState[a].view_num < processState[b].view_num
                               THEN processState[a].commit_num <= Len(processState[b].log)
                               ELSE TRUE

(* Invariant - commit number of other processes <= leader's commit always *)
LeaderCommitNumInv == \A a, b \in 0..NumProcesses-1:
                            \/ a = b
                            \/ IF /\ processState[a].status = "normal"
                                  /\ processState[b].status = "normal"
                                  /\ processState[a].view_num = processState[b].view_num
                                  /\ isLeader(a)
                               THEN processState[a].commit_num >= processState[b].commit_num
                               ELSE TRUE

=============================================================================