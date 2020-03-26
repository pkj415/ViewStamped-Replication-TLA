----------------------- MODULE ViewStampedReplication -----------------------
\* TODO - Model crashes and recoveries of less than majority processes
\* TODO P4 - View change without flooding of start_view_change message.

\* Challenges - running with view change is tough, have to limit the model till a maximum view number.

EXTENDS Integers, Sequences, FiniteSets

CONSTANT
    NumProcesses,   \* The set of processes
    ClientCommands, \* The set of client commands. For now each client has just one command
    MaxViewNum

VARIABLES
    messages,
    processState

PossibleLogSeqences(S) == {possible_seq \in UNION {[1..n -> S] : n \in 0..Cardinality({2, 3})}: (\A a, b \in 1..Len(possible_seq): (a = b \/ possible_seq[a] # possible_seq[b]))}

VRTypeOk == /\ processState \in [0..NumProcesses-1 -> [view_num : 0..MaxViewNum, commit_num: 0..Cardinality(ClientCommands),
                status: {"normal", "view_change", "do_view_change_sent"}, last_active_view_num: 0..MaxViewNum,
                log: PossibleLogSeqences(ClientCommands)]]

VRInit == /\ messages = {}
          /\ processState = 
                    [p \in 0..NumProcesses-1 |-> [view_num |-> 0,
                                   log |-> <<>>,
                                   commit_num |-> 0,
                                   status |-> "normal", \* normal, view_change, do_view_change_sent
                                   last_active_view_num |-> 0
                                   ] 
                    ]

isLeader(p) == \/ processState[p].view_num % NumProcesses = p

sendMsgs(msgs) == messages' = messages \cup msgs

notifyProcesses(p, cmd) == sendMsgs(
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

sendMarkers(p) == /\ sendMsgs(
                        {
                            [type |-> "empty_marker",
                             to |-> listener,
                             from |-> p,
                             view_num |-> processState[p].view_num,
                             commit_num |-> processState[p].commit_num]: listener \in 0..NumProcesses-1 \ {p}
                        }
                     )
                  /\ UNCHANGED <<processState>>

addRequest(p) == /\ \E cmd \in ClientCommands: (
                    /\ (
                        LET set[i \in 0..Len(processState[p].log)] == 
                            IF i = 0 THEN {}
                             ELSE set[i-1] \cup {processState[p].log[i]}
                        IN ~ (cmd \in set[Len(processState[p].log)]))
                    /\ processState' = [processState EXCEPT ![p].log = Append(processState[p].log, cmd)]
                    /\ notifyProcesses(p, cmd)
                  )
                 /\ UNCHANGED <<>>

majorityReplicated(p, log_num) == LET mset == {
                                        msg \in messages: /\ msg.type = "prepareOk"
                                                          /\ msg.view_num = processState[p].view_num
                                                          /\ msg.log_num = log_num
                                                          /\ msg.to = p
                                    }
                                  IN /\ Cardinality(mset) >= NumProcesses \div 2

(* Advance only if log_num > commit_num *)
advanceCommitNumber(p, log_num) == /\ processState' = [processState EXCEPT ![p].commit_num = log_num] 

acceptRequest(p) == /\ \E msg \in messages: (
                        /\ msg.to = p
                        /\ processState[p].view_num = msg.view_num
                        /\ msg.type = "prepare"
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
                      )
                    /\ UNCHANGED <<>>

acceptMarker(p) == /\ \E msg \in messages: (
                        /\ msg.to = p
                        \* In case a higher view number is seen execute some state transfer and catch up. This is needed
                        \* in acceptRequest as well. To handle for every case, add a transition in VRNext itself in case
                        \* the process sees a message for itself with a higher view number. Handle this later.
                        /\ processState[p].view_num = msg.view_num
                        /\ msg.type = "empty_marker"
                        /\ Len(processState[p].log) >= msg.commit_num
                        /\ processState[p].commit_num < msg.commit_num
                        /\ processState' = [processState EXCEPT ![p].commit_num = msg.commit_num]
                      )
                    /\ UNCHANGED <<messages>>

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

normalCaseOperationReplica(p) == acceptRequest(p) \/ acceptMarker(p)

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

sendStartView(p, v, maxLogMsg) == sendMsgs(
                                {
                                    [type |-> "start_view",
                                     to |-> listener,
                                     from |-> p,
                                     log |-> maxLogMsg.log,
                                     view_num |-> v,
                                     commit_num |-> maxLogMsg.commit_num] : listener \in 0..NumProcesses-1 \ {p}
                                }
                             )

recvMajortiyDoViewChange(p, v) == /\ LET
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

VRNext == \/ (\E p \in 0..NumProcesses-1: isLeader(p) /\ processState[p].status = "normal" /\ addRequest(p))
          \/ (\E p \in 0..NumProcesses-1: isLeader(p) /\ processState[p].status = "normal" /\ sendMarkers(p))
          \/ (\E p \in 0..NumProcesses-1: 
                (
                    \* Note that leader can advance commit numbers non-sequentially, keep in mind.
                    /\ isLeader(p)
                    /\ processState[p].status = "normal"
                    /\ \E log_num \in (processState[p].commit_num+1)..Len(processState[p].log): majorityReplicated(p, log_num) /\ (advanceCommitNumber(p, log_num))
                    /\ UNCHANGED <<messages>>
                )
             )
          \/ (\E p \in 0..NumProcesses-1: (~isLeader(p)) /\ normalCaseOperationReplica(p) /\ processState[p].status = "normal")
          \/ (\E p \in 0..NumProcesses-1: viewChangeTransitions(p))
          \/ (\E p \in 0..NumProcesses-1: ( \* ~isLeader(p) is not kept here because it might happen that a leader again becomes the next leader
                \E v \in 0..MaxViewNum:
                    (
                        /\ (
                            \/ v > processState[p].view_num \* TODO - Think of coming up with an invariant which is false in case we just have one condition with v >= processState[p].view_num
                            \/ (v = processState[p].view_num /\ ~(processState[p].status = "normal")) 
                           )
                        /\ v % NumProcesses = p
                        /\ recvMajortiyDoViewChange(p, v)
                    )
                )
             )

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

(* Invariant - process with higher view_num in normal state has larger commit num than process in lower view_num *)
ViewNumCommitNumInv == \A a, b \in 0..NumProcesses-1:
                            \/ a = b
                            \/ IF /\ processState[a].status = "normal"
                                  /\ processState[b].status = "normal"
                                  /\ processState[a].view_num < processState[b].view_num
                               THEN processState[a].commit_num <= processState[b].commit_num
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