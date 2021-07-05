--------------------------------- MODULE raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, Bags, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another.
VARIABLE messages

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
candidateVars == <<votesResponded, votesGranted>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars>>

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) == msgs (+) SetToBag({m})

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) == msgs (-) SetToBag({m})

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Define initial values for all variables

InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
Init == /\ messages = EmptyBag
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log>>

\* Server i times out and starts a new election.
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ UNCHANGED <<messages, leaderVars, logVars>>

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           \* The following upper bound on prevLogIndex is unnecessary
           \* but makes verification substantially simpler.
           prevLogTerm == IF prevLogIndex > 0 /\ prevLogIndex <= Len(log[i]) THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                msource        |-> i,
                mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars>>

\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>

RejectAppendEntriesRequest(i, j, m, logOk) ==
    /\ \/ m.mterm < currentTerm[i]
       \/ /\ m.mterm = currentTerm[i]
          /\ state[i] = Follower
          /\ \lnot logOk
    /\ Reply([mtype           |-> AppendEntriesResponse,
              mterm           |-> currentTerm[i],
              msuccess        |-> FALSE,
              mmatchIndex     |-> 0,
              msource         |-> i,
              mdest           |-> j],
              m)
    /\ UNCHANGED <<serverVars, logVars>>

ReturnToFollowerState(i, m) ==
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Candidate
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>

AppendEntriesAlreadyDone(i, j, index, m) ==
    /\ \/ m.mentries = << >>
       \/ /\ m.mentries /= << >>
          /\ Len(log[i]) >= index
          /\ log[i][index].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
    /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
    /\ Reply([mtype           |-> AppendEntriesResponse,
              mterm           |-> currentTerm[i],
              msuccess        |-> TRUE,
              mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
              msource         |-> i,
              mdest           |-> j],
              m)
    /\ UNCHANGED <<serverVars, logVars>>

ConflictAppendEntriesRequest(i, index, m) ==
    /\ m.mentries /= << >>
    /\ Len(log[i]) >= index
    /\ log[i][index].term /= m.mentries[1].term
    /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |-> log[i][index2]]
       IN log' = [log EXCEPT ![i] = new]
    /\ UNCHANGED <<serverVars, commitIndex, messages>>

NoConflictAppendEntriesRequest(i, m) ==
    /\ m.mentries /= << >>
    /\ Len(log[i]) = m.mprevLogIndex
    /\ log' = [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
    /\ UNCHANGED <<serverVars, commitIndex, messages>>

AcceptAppendEntriesRequest(i, j, logOk, m) ==
    \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ AppendEntriesAlreadyDone(i, j, index, m)
                   \/ ConflictAppendEntriesRequest(i, index, m)
                   \/ NoConflictAppendEntriesRequest(i, m)

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ RejectAppendEntriesRequest(i, j, m, logOk)
          \/ ReturnToFollowerState(i, m)
          \/ AcceptAppendEntriesRequest(i, j, logOk, m)
       /\ UNCHANGED <<candidateVars, leaderVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars>>

\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

----
\* Defines how the variables may transition.
Next == \/ \E i \in Server : Restart(i)
        \/ \E i \in Server : Timeout(i)
        \/ \E i,j \in Server : RequestVote(i, j)
        \/ \E i \in Server : BecomeLeader(i)
        \/ \E i \in Server, v \in Value : ClientRequest(i, v)
        \/ \E i \in Server : AdvanceCommitIndex(i)
        \/ \E i,j \in Server : AppendEntries(i, j)
        \/ \E m \in DOMAIN messages : Receive(m)
        \/ \E m \in DOMAIN messages : DuplicateMessage(m)
        \/ \E m \in DOMAIN messages : DropMessage(m)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The main safety proofs are below                                        *)
(***************************************************************************)
----
\* Type invariants

\* The next four definitions give the types of each type of message
RequestVoteRequestType ==
    [mtype : {RequestVoteRequest},
     mterm : Nat,
     mlastLogTerm : Nat,
     mlastLogIndex : Nat,
     msource : Server,
     mdest : Server]

AppendEntriesRequestType ==
    [mtype : {AppendEntriesRequest},
       mterm : Nat,
       mprevLogIndex : Int,
       mprevLogTerm : Nat,
       mentries : Seq([term : Nat, value : Value]),
       mcommitIndex : Nat,
       msource : Server,
       mdest : Server]

RequestVoteResponseType ==
    [mtype : {RequestVoteResponse},
     mterm : Nat,
     mvoteGranted : BOOLEAN,
     mlog : Seq([term : Nat, value : Value]),
     msource : Server,
     mdest : Server]

AppendEntriesResponseType ==
    [mtype : {AppendEntriesResponse},
     mterm : Nat,
     msuccess : BOOLEAN,
     mmatchIndex : Nat,
     msource : Server,
     mdest : Server]

MessageType ==
    RequestVoteRequestType \cup AppendEntriesRequestType \cup
    RequestVoteResponseType \cup AppendEntriesResponseType

\* The full type invariant for the system
TypeOK ==
    /\ IsABag(messages) /\ BagToSet(messages) \subseteq MessageType
    /\ currentTerm \in [Server -> Nat]
    /\ state \in [Server -> {Follower, Candidate, Leader}]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ log \in [Server -> Seq([term : Nat, value : Value])]
    /\ commitIndex \in [Server -> Nat]
    /\ votesResponded \in [Server -> SUBSET Server]
    /\ votesGranted \in [Server -> SUBSET Server]
    /\ nextIndex \in [Server -> [Server -> { n \in Nat : 1 <= n } ]]
    /\ matchIndex \in [Server -> [Server -> Nat]]

ASSUME DistinctRoles == /\ Leader /= Candidate
                        /\ Candidate /= Follower
                        /\ Follower /= Leader

ASSUME DistinctMessageTypes == /\ RequestVoteRequest /= AppendEntriesRequest
                               /\ RequestVoteRequest /= RequestVoteResponse
                               /\ RequestVoteRequest /= AppendEntriesResponse
                               /\ AppendEntriesRequest /= RequestVoteResponse
                               /\ AppendEntriesRequest /= AppendEntriesResponse
                               /\ RequestVoteResponse /= AppendEntriesResponse

LEMMA WithMessage_IsABag ==
    \A B, m : IsABag(B) => IsABag(WithMessage(m,B))
  BY Bags_SetToBagIsABag, Bags_Union DEF WithMessage

LEMMA WithMessage_MessageType ==
    \A B : IsABag(B) /\ BagToSet(B) \subseteq MessageType =>
           \A m \in MessageType :
                BagToSet(WithMessage(m,B)) \subseteq MessageType
  <1> SUFFICES ASSUME NEW B,
                      IsABag(B) /\ BagToSet(B) \subseteq MessageType,
                      NEW m \in MessageType
               PROVE  BagToSet(WithMessage(m,B)) \subseteq MessageType
    OBVIOUS
  <1>1. DOMAIN (B (+) SetToBag({m})) = DOMAIN B \cup DOMAIN SetToBag({m})
    BY Bags_SetToBagIsABag, Bags_Union
  <1> QED
    BY <1>1 DEF WithMessage, BagToSet, SetToBag

LEMMA WithoutMessage_IsABag ==
    \A B, m : IsABag(B) => IsABag(WithoutMessage(m,B))
  BY Bags_SetToBagIsABag, Bags_Difference DEF WithoutMessage

LEMMA WithoutMessage_MessageType ==
    \A B : IsABag(B) /\ BagToSet(B) \subseteq MessageType =>
           \A m : BagToSet(WithoutMessage(m,B)) \subseteq MessageType
  BY Bags_SetToBagIsABag, Bags_Difference DEF WithoutMessage, BagToSet, SetToBag

LEMMA Reply_messagesType ==
    ASSUME NEW m1 \in MessageType,
           NEW m2 \in MessageType,
           IsABag(messages),
           BagToSet(messages) \subseteq MessageType,
           Reply(m1, m2)
    PROVE  /\ IsABag(messages')
           /\ BagToSet(messages') \subseteq MessageType
<1>1. /\ IsABag(WithMessage(m1, messages))
      /\ BagToSet(WithMessage(m1, messages)) \subseteq MessageType
   BY WithMessage_IsABag, WithMessage_MessageType
<1>2. /\ IsABag(WithoutMessage(m2,WithMessage(m1, messages)))
      /\ BagToSet(WithoutMessage(m2,WithMessage(m1, messages))) \subseteq MessageType
   BY <1>1, WithoutMessage_IsABag, WithoutMessage_MessageType
<1>3. QED
   BY <1>1, <1>2 DEF Reply

LEMMA MaxProperties ==
    ASSUME NEW S \in SUBSET Nat,
           S /= {}
    PROVE /\ Max(S) \in Nat
          /\ \A s \in S : s <= Max(S)
  <1>1. \E x \in S : \A y \in S : ~ <<y, x>> \in OpToRel(<,Nat)
    BY WFMin, NatLessThanWellFounded, IsWellFoundedOnSubset
  <1> QED

LEMMA MinProperties ==
    ASSUME NEW S \in SUBSET Nat,
           S /= {}
    PROVE /\ Min(S) \in Nat
          /\ \A s \in S : Min(S) <= s

\* Type correctness
LEMMA TypeInvariance == Spec => []TypeOK
<1>1. Init => TypeOK
   <2> SUFFICES ASSUME Init
                PROVE  TypeOK
      OBVIOUS
   <2> USE DEF Init
   <2>1. IsABag(messages) /\ BagToSet(messages) \subseteq MessageType
       BY DEF IsABag, EmptyBag, BagToSet, SetToBag
   <2>2. currentTerm \in [Server -> Nat]
       BY DEF InitServerVars
   <2>3. state \in [Server -> {Follower, Candidate, Leader}]
       BY DEF InitServerVars
   <2>4. votedFor \in [Server -> Server \cup {Nil}]
       BY DEF InitServerVars
   <2>5. log \in [Server -> Seq([term : Nat, value : Value])]
       BY DEF InitLogVars
   <2>6. commitIndex \in [Server -> Nat]
       BY DEF InitLogVars
   <2>7. votesResponded \in [Server -> SUBSET Server]
       BY DEF InitCandidateVars
   <2>8. votesGranted \in [Server -> SUBSET Server]
       BY DEF InitCandidateVars
   <2>9. nextIndex \in [Server -> [Server -> { n \in Nat : 1 <= n } ]]
       BY DEF InitLeaderVars
   <2>10. matchIndex \in [Server -> [Server -> Nat]]
       BY DEF InitLeaderVars
   <2>11. QED
      BY <2>1, <2>10, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
   <3> USE DEF TypeOK
   <3> SUFFICES ASSUME TypeOK /\ [Next]_vars
                PROVE  TypeOK'
     OBVIOUS
   <3>1. CASE Next
      <4>1. CASE \E i \in Server : Restart(i)
        BY <4>1 DEF Restart
      <4>2. CASE \E i \in Server : Timeout(i)
        <5> SUFFICES ASSUME NEW i \in Server,
                            Timeout(i)
                     PROVE  TypeOK'
          BY <4>2
        <5> QED
           BY <4>2 DEF Timeout, leaderVars, logVars
      <4>3. CASE \E i,j \in Server : RequestVote(i, j)
        <5> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                            RequestVote(i, j)
                     PROVE  TypeOK'
          BY <4>3
        <5>1. [mtype         |-> RequestVoteRequest,
               mterm         |-> currentTerm[i],
               mlastLogTerm  |-> LastTerm(log[i]),
               mlastLogIndex |-> Len(log[i]),
               msource       |-> i,
               mdest         |-> j] \in MessageType
          BY LenProperties DEF MessageType, LastTerm, RequestVoteRequestType
        <5> QED
          BY <5>1, <4>3, WithMessage_MessageType, WithMessage_IsABag
          DEF RequestVote, serverVars, candidateVars, leaderVars, logVars,
              Send
      <4>4. CASE \E i \in Server : BecomeLeader(i)
        BY <4>4 DEF BecomeLeader, candidateVars, logVars
      <4>5. CASE \E i \in Server, v \in Value : ClientRequest(i, v)
         BY <4>5, AppendProperties
         DEF ClientRequest, candidateVars, leaderVars, serverVars
      <4>6. CASE \E i \in Server : AdvanceCommitIndex(i)
        <5> USE DEF AdvanceCommitIndex  
        <5> SUFFICES ASSUME NEW i \in Server,
                            AdvanceCommitIndex(i)
                     PROVE  TypeOK'
          BY <4>6 
        <5>1. (commitIndex \in [Server -> Nat])'
            <6>1. {index \in 1..Len(log[i]) :
                              {i}
                              \cup {k \in Server : matchIndex[i][k] >= index}
                              \in Quorum} \in SUBSET Nat
                BY LenProperties
            <6>2. ASSUME {index \in 1..Len(log[i]) :
                              {i}
                              \cup {k \in Server : matchIndex[i][k] >= index}
                              \in Quorum}
                           # {}
                  PROVE   Max({index \in 1..Len(log[i]) :
                                    {i}
                                    \cup {k \in Server :
                                            matchIndex[i][k] >= index}
                                    \in Quorum}) \in Nat
                BY <6>1, <6>2, MaxProperties
            <6>3. QED
                BY <6>2
        <5>2. QED
          BY <5>1 DEF serverVars, logVars, candidateVars, leaderVars
      <4>7. CASE \E i,j \in Server : AppendEntries(i, j)
        <5> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                            AppendEntries(i, j)
                     PROVE  TypeOK'
          BY <4>7
        <5> state[i] = Leader
           BY DEF AppendEntries 
        <5> DEFINE m ==
               [mtype |-> AppendEntriesRequest,
                mterm |-> currentTerm[i],
                mprevLogIndex |-> nextIndex[i][j] - 1,
                mprevLogTerm |-> IF nextIndex[i][j] - 1 > 0 /\ nextIndex[i][j] - 1 <= Len(log[i])
                                 THEN log[i][nextIndex[i][j] - 1].term
                                 ELSE 0,
                mentries |-> SubSeq(log[i], nextIndex[i][j],
                                    Min({Len(log[i]), nextIndex[i][j]})),
                mcommitIndex |-> Min({commitIndex[i],
                                      Min({Len(log[i]), nextIndex[i][j]})}),
                msource |-> i, mdest |-> j]
        <5>1. Min({Len(log[i]), nextIndex[i][j]}) \in Nat
            BY MinProperties, LenProperties
        <5>2. Min({commitIndex[i], Min({Len(log[i]), nextIndex[i][j]})}) \in Nat
            <6>1. {commitIndex[i], Min({Len(log[i]), nextIndex[i][j]})} /= {}
                OBVIOUS
            <6>2. commitIndex[i] \in Nat
                OBVIOUS
            <6> QED
                BY MinProperties, <5>1, <6>1, <6>2
        <5>3. m.mentries \in Seq([term : Nat, value : Value])
            BY SubSeqProperties, MinProperties
        <5>4. m.mprevLogTerm \in Nat
            OBVIOUS
        <5>5. m.mprevLogIndex \in Int
            OBVIOUS
        <5>6. m \in MessageType
            BY <5>2, <5>3, <5>4, <5>5
            DEF MessageType, AppendEntriesRequestType
        <5> QED
          BY <4>7, <5>6, WithMessage_MessageType, WithMessage_IsABag
          DEF AppendEntries, serverVars, candidateVars, leaderVars, logVars, Send
      <4>8. CASE \E m \in DOMAIN messages : Receive(m)
        <5> USE DEF Receive
        <5> SUFFICES ASSUME NEW m \in DOMAIN messages,
                            Receive(m)
                     PROVE  TypeOK'
          BY <4>8
        <5> DEFINE i == m.mdest
        <5> DEFINE j == m.msource
        <5>0. i \in Server /\ j \in Server
           BY DEF BagToSet, MessageType, RequestVoteRequestType,
                  AppendEntriesRequestType, RequestVoteResponseType,
                  AppendEntriesResponseType
        <5>1. CASE UpdateTerm(i, j, m)
           <6>1. m \in MessageType
              BY DEF BagToSet
           <6>2. m.mterm \in Nat
              BY <6>1
              DEF MessageType, RequestVoteRequestType,
                  AppendEntriesRequestType, RequestVoteResponseType,
                  AppendEntriesResponseType
           <6> QED
              BY <5>1, <6>2, DistinctRoles
              DEF UpdateTerm, candidateVars, leaderVars, logVars
        <5>2. CASE /\ m.mtype = RequestVoteRequest
                   /\ HandleRequestVoteRequest(i, j, m)
           <6> DEFINE logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                               \/ /\ m.mlastLogTerm = LastTerm(log[i])
                                  /\ m.mlastLogIndex >= Len(log[i])
           <6> DEFINE grant == /\ m.mterm = currentTerm[i]
                               /\ logOk
                               /\ votedFor[i] \in {Nil, j}
           <6> DEFINE m_1 == [mtype        |-> RequestVoteResponse,
                            mterm        |-> currentTerm[i],
                            mvoteGranted |-> grant,
                            mlog         |-> log[i],
                            msource      |-> i,
                            mdest        |-> j]
                     
           <6>2. m_1 \in MessageType
              BY <5>0 DEF MessageType, RequestVoteResponseType
           <6>3. m \in MessageType
              BY DEF BagToSet
           <6>4. /\ IsABag(WithMessage(m_1, messages))
                 /\ BagToSet(WithMessage(m_1, messages)) \subseteq MessageType
              BY <6>2, WithMessage_IsABag, WithMessage_MessageType
           <6>5. /\ IsABag(WithoutMessage(m,WithMessage(m_1, messages)))
                 /\ BagToSet(WithoutMessage(m,WithMessage(m_1, messages))) \subseteq MessageType
              BY <6>3, <6>4, WithoutMessage_IsABag, WithoutMessage_MessageType
           <6>6. IsABag(messages') /\ BagToSet(messages') \subseteq MessageType
              BY <5>2, <6>5 DEF HandleRequestVoteRequest, Reply
           <6> QED
              BY <5>2, <5>0, <6>2, <6>6
              DEF HandleRequestVoteRequest, leaderVars, candidateVars, logVars
        <5>3. CASE /\ m.mtype = RequestVoteResponse
                   /\ \/ DropStaleResponse(m.mdest, m.msource, m)
                      \/ HandleRequestVoteResponse(m.mdest, m.msource, m)
           <6>1. m \in MessageType
              BY DEF BagToSet
           <6>2. CASE DropStaleResponse(i, j, m)
              BY <5>3, <6>1, <6>2, WithoutMessage_IsABag,
                  WithoutMessage_MessageType
              DEF DropStaleResponse, Discard, serverVars,
                  candidateVars, leaderVars, logVars
           <6>3. CASE HandleRequestVoteResponse(i, j, m)
                BY <5>0, <5>3, <6>1, <6>3, WithoutMessage_IsABag,
                   WithoutMessage_MessageType
                DEF HandleRequestVoteResponse, Discard,
                    serverVars, leaderVars, logVars
           <6> QED
              BY <5>3, <6>2, <6>3
        <5>4. CASE /\ m.mtype = AppendEntriesRequest
                   /\ HandleAppendEntriesRequest(i, j, m)
           <6> m \in MessageType
              BY DEF MessageType, AppendEntriesRequestType, BagToSet
           <6>0. m \in AppendEntriesRequestType
                 BY <5>4, DistinctMessageTypes
                 DEF MessageType, RequestVoteRequestType, AppendEntriesRequestType,
                     RequestVoteResponseType, AppendEntriesResponseType
           <6> DEFINE logOk == \/ m.mprevLogIndex = 0
                               \/ /\ m.mprevLogIndex > 0
                                  /\ m.mprevLogIndex <= Len(log[i])
                                  /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
           <6>1. CASE RejectAppendEntriesRequest(i, j, m, logOk)
              <7> DEFINE m_1 ==
                     [mtype |-> AppendEntriesResponse,
                      mterm |-> currentTerm[m.mdest], msuccess |-> FALSE,
                      mmatchIndex |-> 0, msource |-> m.mdest,
                      mdest |-> m.msource]
              <7>1. m_1 \in MessageType
                BY <5>0 DEF MessageType, AppendEntriesResponseType
              <7> QED
                 BY <5>4, <6>1, <7>1, Reply_messagesType
                 DEF HandleAppendEntriesRequest, RejectAppendEntriesRequest,
                     serverVars, logVars, candidateVars, leaderVars
           <6>2. CASE ReturnToFollowerState(i, m)
              BY <5>4, <6>2, DistinctRoles
              DEF HandleAppendEntriesRequest, ReturnToFollowerState, logVars,
                  candidateVars, leaderVars
           <6>3. CASE AcceptAppendEntriesRequest(i, j, logOk, m)
              <7> DEFINE index == m.mprevLogIndex + 1
              <7>0. state[i] = Follower
                BY <6>3 DEF AcceptAppendEntriesRequest
              <7>2. m.mprevLogIndex \in Nat
                BY <6>3, <6>0
                DEF AcceptAppendEntriesRequest, AppendEntriesRequestType
              <7>3. CASE AppendEntriesAlreadyDone(i, j, index, m)
                 <8>1. [mtype |-> AppendEntriesResponse,
                        mterm |-> currentTerm[m.mdest], msuccess |-> TRUE,
                        mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                        msource |-> m.mdest, mdest |-> m.msource] \in MessageType
                    BY <5>0, <6>0, <7>2, LenProperties
                    DEF MessageType, AppendEntriesRequestType, AppendEntriesResponseType
                 <8> QED
                    BY <5>4, <7>2, <8>1, <7>3, Reply_messagesType
                    DEF AppendEntriesAlreadyDone, HandleAppendEntriesRequest,
                        AppendEntriesRequestType, candidateVars, leaderVars,
                        serverVars, logVars
              <7>4. CASE ConflictAppendEntriesRequest(i, index, m)
                <8>1. [index2 \in 1..Len(log[m.mdest]) - 1 |->
                               log[m.mdest][index2]]
                      \in Seq([term : Nat, value : Value])
                   BY <5>0
                <8>2. [log EXCEPT
                           ![m.mdest] = [index2 \in 1..Len(log[m.mdest]) - 1 |->
                                        log[m.mdest][index2]]]
                      \in [Server -> Seq([term : Nat, value : Value])]
                   BY <8>1
                <8>3. log' \in [Server -> Seq([term : Nat, value : Value])]
                   BY <8>2, <7>4 DEF ConflictAppendEntriesRequest
                <8>4. UNCHANGED <<messages, currentTerm, state, votedFor, commitIndex,
                                  votesResponded, votesGranted, nextIndex, matchIndex>>
                   BY <5>4, <7>4
                   DEF HandleAppendEntriesRequest, ConflictAppendEntriesRequest,
                       serverVars, candidateVars, leaderVars
                <8> QED
                    BY <8>3, <8>4, <7>0, <7>4, DistinctRoles
                    DEF ConflictAppendEntriesRequest
              <7>5. CASE NoConflictAppendEntriesRequest(i, m)
                <8>1. UNCHANGED <<messages, currentTerm, state, votedFor, commitIndex,
                                  votesResponded, votesGranted, nextIndex, matchIndex>>
                   BY <5>4, <7>5
                   DEF HandleAppendEntriesRequest, NoConflictAppendEntriesRequest,
                       serverVars, candidateVars, leaderVars
                <8>2. Append(log[m.mdest], (m.mentries)[1])
                      \in Seq([term : Nat, value : Value])
                   BY <7>5, <5>0, <6>0, AppendProperties
                   DEF AppendEntriesRequestType, NoConflictAppendEntriesRequest
                <8> QED
                   BY <7>0, <7>5, <8>1, <8>2, DistinctRoles
                   DEF NoConflictAppendEntriesRequest
              <7> QED
                BY <5>4, <6>3, <7>3, <7>4, <7>5
                DEF AcceptAppendEntriesRequest, candidateVars, leaderVars
           <6> QED
              BY <5>4, <6>1, <6>2, <6>3 DEF HandleAppendEntriesRequest
        <5>5. CASE /\ m.mtype = AppendEntriesResponse
                   /\ \/ DropStaleResponse(i, j, m)
                      \/ HandleAppendEntriesResponse(i, j, m)
           <6>1. CASE DropStaleResponse(i, j, m)
              BY <6>1, WithoutMessage_IsABag, WithoutMessage_MessageType
              DEF DropStaleResponse, Discard,
                  serverVars, candidateVars, leaderVars, logVars
           <6>2. CASE HandleAppendEntriesResponse(i, j, m)
              <7>1. m \in AppendEntriesResponseType
                 BY <5>5, DistinctMessageTypes
                 DEF BagToSet, MessageType, AppendEntriesResponseType,
                     RequestVoteRequestType, AppendEntriesRequestType,
                     RequestVoteResponseType
              <7> QED
                 BY <6>2, <7>1, WithoutMessage_IsABag, WithoutMessage_MessageType,
                    MaxProperties
                 DEF HandleAppendEntriesResponse, Discard, AppendEntriesResponseType,
                     serverVars, candidateVars, logVars 
           <6> QED
              BY <5>5, <6>1, <6>2
        <5> QED
            BY <5>1, <5>2, <5>3, <5>4, <5>5
      <4>9. CASE \E m \in DOMAIN messages : DuplicateMessage(m)
        BY <4>9, WithMessage_IsABag, WithMessage_MessageType
        DEF DuplicateMessage, Send, leaderVars, serverVars, candidateVars,
            logVars, BagToSet
      <4>10. CASE \E m \in DOMAIN messages : DropMessage(m)
        BY <4>10, WithoutMessage_IsABag, WithoutMessage_MessageType
        DEF DropMessage, Discard, leaderVars, serverVars, candidateVars,
            logVars, BagToSet
      <4>11. QED
        BY <3>1, <4>1, <4>10, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9
        DEF Next
    <3>2. CASE UNCHANGED vars
        BY <3>2 DEF vars, serverVars, candidateVars, leaderVars, logVars
    <3>3. QED
      BY <3>1, <3>2
<1>3. QED
   BY <1>1, <1>2, PTL DEF Spec

----
\* Correctness invariants

\* The prefix of the log of server i that has been committed
Committed(i) == SubSeq(log[i],1,commitIndex[i])

----
\* Invariants for messages

\* If server i casts a vote for server j and their terms
\* are the same, then i's committed log is a prefix of j's log
RequestVoteResponseInv(m) ==
    m \in RequestVoteResponseType =>
        ((/\ m.mvoteGranted
          /\ currentTerm[m.msource] = currentTerm[m.mdest]
          /\ currentTerm[m.msource] = m.mterm) =>
         (\/ LastTerm(log[m.mdest]) > LastTerm(log[m.msource])
          \/ /\ LastTerm(log[m.mdest]) = LastTerm(log[m.msource])
             /\ Len(log[m.dest]) >= Len(log[m.msource])))

\* Request vote messages give at most the last log
\* index and term of the requester, as long as the requester
\* is a Candidate
RequestVoteRequestInv(m) ==
    m \in RequestVoteRequestType =>
       ((/\ state[m.msource] = Candidate
         /\ currentTerm[m.msource] = m.mterm) =>
        (/\ m.mlastLogIndex = Len(log[m.msource])
         /\ m.mlastLogTerm = LastTerm(log[m.msource])))

\* Append entries requests give the correct previous term
\* and index of the source server
AppendEntriesRequestInv(m) ==
    m \in AppendEntriesRequestType =>
      ((/\ m.mentries /= << >>
        /\ m.mterm = currentTerm[m.msource]) =>
       (/\ log[m.msource][m.mprevLogIndex + 1] = m.mentries[1]
        /\ m.mprevLogIndex > 0 /\ m.mprevLogIndex <= Len(log[m.msource])=>
           log[m.msource][m.mprevLogIndex].term = m.mprevLogTerm))

\* The current term of any server is at least the term
\* of any message sent by that server
MessageTermsLtCurrentTerm(m) ==
    m.mterm <= currentTerm[m.msource]

\* This invariant encodes everything in messages
\* that is necessary for safety. I don't think that
\* AppendEntriesResponses are relevant to safety,
\* only progress.
MessagesInv ==
    \A m \in DOMAIN messages :
        /\ RequestVoteResponseInv(m)
        /\ RequestVoteRequestInv(m)
        /\ AppendEntriesRequestInv(m)
        /\ MessageTermsLtCurrentTerm(m)

LEMMA MessagesCorrect == Spec => []MessagesInv
<1> USE DEF MessagesInv
<1>1. Init => MessagesInv
    BY DEF Init, EmptyBag, SetToBag
<1>2. MessagesInv /\ TypeOK /\ [Next]_vars => MessagesInv'
  <2> SUFFICES ASSUME MessagesInv,
                      TypeOK,
                      [Next]_vars
               PROVE  MessagesInv'
    OBVIOUS
  <2>1. CASE \E i \in Server : Restart(i)
    <3> USE <2>1 DEF Restart
    <3> SUFFICES ASSUME NEW m \in (DOMAIN messages)'
                 PROVE  (/\ RequestVoteResponseInv(m)
                         /\ RequestVoteRequestInv(m)
                         /\ AppendEntriesRequestInv(m)
                         /\ MessageTermsLtCurrentTerm(m))'
      BY DEF MessagesInv
    <3>1. RequestVoteResponseInv(m)'
      BY DEF RequestVoteResponseInv
    <3>2. RequestVoteRequestInv(m)'
      BY DistinctRoles
      DEF RequestVoteRequestInv, TypeOK, RequestVoteRequestType
    <3>3. AppendEntriesRequestInv(m)'
      BY DEF AppendEntriesRequestInv, TypeOK, AppendEntriesRequestType
    <3>4. MessageTermsLtCurrentTerm(m)'
      BY DEF MessageTermsLtCurrentTerm
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4
  <2>2. CASE \E i \in Server : Timeout(i)
    <3> USE <2>2 DEF Timeout
    <3> SUFFICES ASSUME NEW m \in (DOMAIN messages)'
                 PROVE  (/\ RequestVoteResponseInv(m)
                         /\ RequestVoteRequestInv(m)
                         /\ AppendEntriesRequestInv(m)
                         /\ MessageTermsLtCurrentTerm(m))'
      BY DEF MessagesInv
    <3>1. RequestVoteResponseInv(m)'
      BY DEF RequestVoteResponseInv, logVars, TypeOK, RequestVoteResponseType
    <3>2. RequestVoteRequestInv(m)'
    <3>3. AppendEntriesRequestInv(m)'
    <3>4. MessageTermsLtCurrentTerm(m)'
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4
  <2>3. ASSUME NEW i \in Server,
               NEW j \in Server,
               RequestVote(i, j)
        PROVE  MessagesInv'
    BY <2>3 DEF RequestVote
  <2>4. CASE \E i \in Server : BecomeLeader(i)
    BY <2>4 DEF BecomeLeader
  <2>5. CASE \E i \in Server, v \in Value : ClientRequest(i, v)
    BY <2>5 DEF ClientRequest
  <2>6. CASE \E i \in Server : AdvanceCommitIndex(i)
    BY <2>6 DEF AdvanceCommitIndex
  <2>7. ASSUME NEW i \in Server,
               NEW j \in Server,
               AppendEntries(i, j)
        PROVE  MessagesInv'
    BY <2>7 DEF MessagesInv
  <2>8. ASSUME NEW m \in DOMAIN messages,
               Receive(m)
        PROVE  MessagesInv'
    BY <2>8 DEF MessagesInv
  <2>9. CASE \E m \in DOMAIN messages : DuplicateMessage(m)
    BY <2>9
  <2>10. CASE \E m \in DOMAIN messages : DropMessage(m)
    BY <2>10
  <2>11. CASE UNCHANGED vars
    BY <2>11 DEF vars
  <2>12. QED
    BY <2>1, <2>10, <2>11, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next
<1>3. QED
    BY <1>1, <1>2, PTL, TypeInvariance DEF Spec

----
\* I believe that the election safety property in the Raft
\* paper is stronger than it needs to be and requires history
\* variables. The definition ElectionSafety is an invariant that
\* is strong enough without requiring history variables. First,
\* we state two properties which will allow us to conclude election
\* safety

\* All leaders have a quorum of servers who either voted
\* for the leader or have a higher term
LeaderVotesQuorum ==
    \A i \in Server :
        state[i] = Leader =>
        {j \in Server : currentTerm[j] > currentTerm[i] \/
                        (currentTerm[j] = currentTerm[i] /\ votedFor[j] = i)} \in Quorum

\* If a candidate has a chance of being elected, there
\* are no log entries with that candidate's term
CandidateTermNotInLog ==
    \A i \in Server :
        (/\ state[i] = Candidate
         /\ {j \in Server : currentTerm[j] = currentTerm[i] /\ votedFor[j] \in {i, Nil}} \in Quorum) =>
        \A j \in Server :
        \A n \in DOMAIN log[j] :
             log[j][n].term /= currentTerm[i]

LEMMA ElectionsCorrect == Spec => [](CandidateTermNotInLog /\ LeaderVotesQuorum)
<1>1. Init => CandidateTermNotInLog /\ LeaderVotesQuorum
  <2> USE DEF Init
  <2> SUFFICES ASSUME Init
               PROVE  CandidateTermNotInLog /\ LeaderVotesQuorum
    OBVIOUS
  <2>1. CandidateTermNotInLog
    BY DistinctRoles DEF CandidateTermNotInLog, InitServerVars
  <2>2. LeaderVotesQuorum
    BY DistinctRoles DEF LeaderVotesQuorum, InitServerVars
  <2>3. QED
    BY <2>1, <2>2
<1>2. CandidateTermNotInLog /\ LeaderVotesQuorum /\ TypeOK /\ TypeOK' /\ [Next]_vars =>
      (CandidateTermNotInLog' /\ LeaderVotesQuorum')
  <2> USE DEF TypeOK
  <2> SUFFICES ASSUME CandidateTermNotInLog,
                      LeaderVotesQuorum,
                      TypeOK,
                      TypeOK',
                      [Next]_vars
               PROVE  CandidateTermNotInLog' /\ LeaderVotesQuorum'
    OBVIOUS
  <2>1. ASSUME NEW i \in Server,
               Restart(i)
        PROVE  CandidateTermNotInLog' /\ LeaderVotesQuorum'
    BY <2>1, DistinctRoles
    DEF Restart, CandidateTermNotInLog, LeaderVotesQuorum, Quorum
  <2>2. ASSUME NEW i \in Server,
               Timeout(i)
        PROVE  CandidateTermNotInLog' /\ LeaderVotesQuorum'
    <3> USE <2>2 DEF Timeout
    <3>1. CandidateTermNotInLog'
    <3>2. LeaderVotesQuorum'
        BY DistinctRoles DEF LeaderVotesQuorum, Quorum, logVars
    <3>3. QED
      BY <3>1, <3>2
  <2>3. ASSUME NEW i \in Server,
               NEW j \in Server,
               RequestVote(i, j)
        PROVE  CandidateTermNotInLog' /\ LeaderVotesQuorum'
    BY <2>3
    DEF RequestVote, CandidateTermNotInLog, LeaderVotesQuorum, Quorum,
        logVars, serverVars
  <2>4. ASSUME NEW i \in Server,
               BecomeLeader(i)
        PROVE  CandidateTermNotInLog' /\ LeaderVotesQuorum'
    BY <2>4
    DEF BecomeLeader, CandidateTermNotInLog, LeaderVotesQuorum, Quorum
  <2>5. ASSUME NEW i \in Server,
               NEW v \in Value,
               ClientRequest(i, v)
        PROVE  CandidateTermNotInLog' /\ LeaderVotesQuorum'
  <2>6. ASSUME NEW i \in Server,
               AdvanceCommitIndex(i)
        PROVE  CandidateTermNotInLog' /\ LeaderVotesQuorum'
  <2>7. ASSUME NEW i \in Server,
               NEW j \in Server,
               AppendEntries(i, j)
        PROVE  CandidateTermNotInLog' /\ LeaderVotesQuorum'
  <2>8. ASSUME NEW m \in DOMAIN messages,
               Receive(m)
        PROVE  CandidateTermNotInLog' /\ LeaderVotesQuorum'
  <2>9. ASSUME NEW m \in DOMAIN messages,
               DuplicateMessage(m)
        PROVE  CandidateTermNotInLog' /\ LeaderVotesQuorum'
  <2>10. ASSUME NEW m \in DOMAIN messages,
                DropMessage(m)
         PROVE  CandidateTermNotInLog' /\ LeaderVotesQuorum'
  <2>11. CASE UNCHANGED vars
  <2>12. QED
    BY <2>1, <2>10, <2>11, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next
<1>3. QED
    BY <1>1, <1>2, PTL, TypeInvariance DEF Spec

\* A leader always has the greatest index for its current term
ElectionSafety ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server :
            Max({n \in DOMAIN log[i] : log[i][n].term = currentTerm[i]}) >=
            Max({n \in DOMAIN log[j] : log[j][n].term = currentTerm[i]})
----
\* Every (index, term) pair determines a log prefix
LogMatching ==
    \A i, j \in Server :
        \A n \in (1..Len(log[i])) \cap (1..Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)
----
\* A leader has all committed entries in its log. This is expressed
\* by LeaderCompleteness below. The inductive invariant for
\* that property is the conjunction of LeaderCompleteness with the
\* other three properties below.

\* Votes are only granted to servers with logs
\* that are at least as up to date
VotesGrantedInv ==
    \A i \in Server :
    \A j \in votesGranted[i] :
        currentTerm[i] = currentTerm[j] =>
        \* The following is a subtlety:
        \* Only the committed entries of j are
        \* a prefix of i's log, not the entire 
        \* log of j
        IsPrefix(Committed(j),log[i])

\* All committed entries are contained in the log
\* of at least one server in every quorum
QuorumLogInv ==
    \A i \in Server :
    \A S \in Quorum :
        \E j \in S :
            IsPrefix(Committed(i), log[j])

\* The "up-to-date" check performed by servers
\* before issuing a vote implies that i receives
\* a vote from j only if i has all of j's committed
\* entries
MoreUpToDateCorrect ==
    \A i, j \in Server :
       (\/ LastTerm(log[i]) > LastTerm(log[j])
        \/ /\ LastTerm(log[i]) = LastTerm(log[j])
           /\ Len(log[i]) >= Len(log[j])) =>
       IsPrefix(Committed(j), log[i])

\* The committed entries in every log are a prefix of the
\* leader's log
LeaderCompleteness ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server :
            IsPrefix(Committed(j),log[i])

===============================================================================

\* Changelog:
\*
\* 2014-12-02:
\* - Fix AppendEntries to only send one entry at a time, as originally
\*   intended. Since SubSeq is inclusive, the upper bound of the range should
\*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
\*   reporting the issue.
\* - Change matchIndex' to matchIndex (without the apostrophe) in
\*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
\*   confusing, though it makes no practical difference (matchIndex' equals
\*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
\*
\* 2014-07-06:
\* - Version from PhD dissertation
