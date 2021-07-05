--------------------------------- MODULE raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro, 2016 Daniel Ricketts,
\* 2021 George Pîrlea and Darius Foo.
\*
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, Integers, TypedBags, FiniteSets, Sequences, SequencesExt, TLC


\* The set of server IDs
CONSTANTS 
    \* @type: Set(Int);
    Server

\* Constraints
MaxLogLength == 5
MaxRestarts == 2
MaxTimeouts == 2
MaxInFlightMessages == LET card == 2 * Cardinality(Server) IN card * card

\* The set of requests that can go into the log
CONSTANTS 
    \* @type: Set(Int);
    Value

\* Server states.
CONSTANTS 
    \* @type: Str;
    Follower,
    \* @type: Str;
    Candidate,
    \* @type: Str;
    Leader

\* A reserved value.
CONSTANTS 
    \* @type: Int;
    Nil

\* Message types:
CONSTANTS 
    \* @type: Str;
    RequestVoteRequest,
    \* @type: Str;
    RequestVoteResponse,
    \* @type: Str;
    AppendEntriesRequest,
    \* @type: Str;
    AppendEntriesResponse

-----

\* Message types

EmptyRVReqMsg == [
    mtype         |-> RequestVoteRequest,
    mterm         |-> 0,
    mlastLogTerm  |-> 0,
    mlastLogIndex |-> 0,
    msource       |-> Nil,
    mdest         |-> Nil
]

EmptyAEReqMsg == [
    mtype          |-> AppendEntriesRequest,
    mterm          |-> 0,
    mprevLogIndex  |-> 0,
    mprevLogTerm   |-> 0,
    mentries       |-> << >>,
    mcommitIndex   |-> Nil,
    msource        |-> Nil,
    mdest          |-> Nil
]

EmptyRVRespMsg == [
    mtype        |-> RequestVoteResponse,
    mterm        |-> Nil,
    mvoteGranted |-> FALSE,
    mlog         |-> << >>,
    msource      |-> Nil,
    mdest        |-> Nil
]

EmptyAERespMsg == [
    mtype           |-> AppendEntriesResponse,
    mterm           |-> 0,
    msuccess        |-> FALSE,
    mmatchIndex     |-> 0,
    msource         |-> Nil,
    mdest           |-> Nil
]

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. We differentiate between the message types to support Apalache.
VARIABLE
    \* @typeAlias: ENTRY = [term: Int, value: Int];
    \* @typeAlias: LOGT = Seq(ENTRY);
    \* @typeAlias: RVREQT = [mtype: Str, mterm: Int, mlastLogTerm: Int, mlastLogIndex: Int, msource: Int, mdest: Int];
    \* @typeAlias: RVRESPT = [mtype: Str, mterm: Int, mvoteGranted: Bool, mlog: LOGT, msource: Int, mdest: Int ];
    \* @typeAlias: AEREQT = [mtype: Str, mterm: Int, mprevLogIndex: Int, mprevLogTerm: Int, mentries: LOGT, mcommitIndex: Int, msource: Int, mdest: Int ];
    \* @typeAlias: AERESPT = [mtype: Str, mterm: Int, msuccess: Bool, mmatchIndex: Int, msource: Int, mdest: Int ];
    \* @typeAlias: MSG = [ wrapped: Bool, mtype: Str, mterm: Int, msource: Int, mdest: Int, RVReq: RVREQT, RVResp: RVRESPT, AEReq: AEREQT, AEResp: AERESPT ];
    \* @type: MSG -> Int;
    messages

\* history variable used to constraining the search space
\* restarted: how many times each server restarted
VARIABLE
    \* @typeAlias: ACTION = [action: Str, executedOn: Int, msg: MSG];
    \* @type: [server: Int -> [restarted: Int, timeout: Int], global: Seq(ACTION), hadAtLeastOneLeader: Bool];
    history

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE 
    \* @type: Int -> Int;
    currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE 
    \* @type: Int -> Str;
    state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE 
    \* @type: Int -> Int;
    votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE 
    \* @type: Int -> LOGT;
    log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE 
    \* @type: Int -> Int;
    commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE 
    \* @type: Int -> Set(Int);
    votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE 
    \* @type: Int -> Set(Int);
    votesGranted
\* @type: Seq(Int -> Set(Int));
candidateVars == <<votesResponded, votesGranted>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE 
    \* @type: Int -> (Int -> Int);
    nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE 
    \* @type: Int -> (Int -> Int);
    matchIndex
\* @type: Seq(Int -> (Int -> Int));
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
\* @type: LOGT => Int;
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
\* @type: (MSG, MSG -> Int) => MSG -> Int;
WithMessage(m, msgs) == msgs (+) SetToBag({m})

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
\* @type: (MSG, MSG -> Int) => MSG -> Int;
WithoutMessage(m, msgs) == msgs (-) SetToBag({m})

\* @type: a => MSG;
WrapMsg(m) == 
    IF "wrapped" \notin DOMAIN m THEN
        IF m.mtype = RequestVoteRequest THEN
            [ wrapped |-> TRUE, mtype |-> m.mtype, mterm |-> m.mterm, msource |-> m.msource, mdest |-> m.mdest, RVReq |-> m, RVResp |-> EmptyRVRespMsg, AEReq |-> EmptyAEReqMsg, AEResp |-> EmptyAERespMsg ]
        ELSE IF m.mtype = RequestVoteResponse THEN
            [ wrapped |-> TRUE, mtype |-> m.mtype, mterm |-> m.mterm, msource |-> m.msource, mdest |-> m.mdest, RVReq |-> EmptyRVReqMsg, RVResp |-> m, AEReq |-> EmptyAEReqMsg, AEResp |-> EmptyAERespMsg ]
        ELSE IF m.mtype = AppendEntriesRequest THEN
            [ wrapped |-> TRUE, mtype |-> m.mtype, mterm |-> m.mterm, msource |-> m.msource, mdest |-> m.mdest, RVReq |-> EmptyRVReqMsg, RVResp |-> EmptyRVRespMsg, AEReq |-> m, AEResp |-> EmptyAERespMsg ]
        ELSE
            [ wrapped |-> TRUE, mtype |-> m.mtype, mterm |-> m.mterm, msource |-> m.msource, mdest |-> m.mdest, RVReq |-> EmptyRVReqMsg, RVResp |-> EmptyRVRespMsg, AEReq |-> EmptyAEReqMsg, AEResp |-> m ]
    ELSE m

\* Add a message to the bag of messages.
\* @type: [msource: Int] => Bool;
Send(m) == 
    LET w == WrapMsg(m) IN
    LET action == [action |-> "Send", executedOn |-> m.msource, msg |-> w] IN
    /\ messages'    = WithMessage(w, messages)
    /\ history'     = [history EXCEPT !["global"] = Append(history["global"], action)]

\* Used by the environment to duplicate messges.
\* @type: [msource: Int] => Bool;
SendWithoutHistory(m) == 
    LET w == WrapMsg(m) IN
    messages' = WithMessage(w, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
\* @type: [mdest: Int] => Bool;
Discard(m) ==
    LET w == WrapMsg(m) IN
    LET action == [action |-> "Receive", executedOn |-> m.mdest, msg |-> w] IN
    /\ messages'    = WithoutMessage(w, messages)
    /\ history'     = [history EXCEPT !["global"] = Append(history["global"], action)]

\* Used by the environment to drop messges.
\* @type: a => Bool;
DiscardWithoutHistory(m) ==
    LET w == WrapMsg(m) IN
    messages' = WithoutMessage(w, messages)

\* Combination of Send and Discard
\* @type: ([msource: Int], [mdest: Int]) => Bool;
Reply(response, request) ==
    LET wreq == WrapMsg(request) IN
    LET wresp == WrapMsg(response) IN
    LET recvA == [action |-> "Receive", executedOn |-> request.mdest, msg |-> wreq] IN
    LET respA == [action |-> "Send", executedOn |-> response.msource, msg |-> wresp] IN
    /\ messages'    = WithoutMessage(wreq, WithMessage(wresp, messages))
    /\ history'     = [history EXCEPT !["global"] = Append(Append(history["global"], recvA), respA)]

\* Return the minimum value from a set, or undefined if the set is empty.
\* @type: Set(Int) => Int;
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
\* @type: Set(Int) => Int;
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
InitHistory == [
    server |-> [i \in Server |-> [restarted |-> 0, timeout |-> 0]],
    global |-> << >>,
    hadAtLeastOneLeader |-> FALSE
]

Init == /\ messages = EmptyBag
        /\ history  = InitHistory
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
\* @type: Int => Bool;
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ history'        = [history EXCEPT
                                !["server"] [i] ["restarted"] = history["server"][i]["restarted"] + 1,
                                !["global"] = Append(history["global"], [action |-> "Restart", executedOn |-> i])]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log>>

\* Server i times out and starts a new election.
\* @type: Int => Bool;
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ history'        = [history EXCEPT 
                                        !["server"] [i] ["timeout"] = history["server"][i]["timeout"] + 1,
                                        !["global"] = Append(history["global"], [action |-> "Timeout", executedOn |-> i])]
              /\ UNCHANGED <<messages, leaderVars, logVars>>

\* Candidate i sends j a RequestVote request.
\* @type: (Int, Int) => Bool;
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
\* @type: (Int, Int) => Bool;
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
\* @type: Int => Bool;
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ history'    = [history EXCEPT !["hadAtLeastOneLeader"] = TRUE]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars>>
    
\* Leader i receives a client request to add v to the log.
\* @type: (Int, Int) => Bool;
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex, history>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
\* @type: Int => Bool;
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \*  logSize == Len(log[i])
           logSize == MaxLogLength
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..MaxLogLength :
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
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, history>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
\* @type: (Int, Int, RVREQT) => Bool;
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
\* @type: (Int, Int, RVRESPT) => Bool;
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

\* @type: (Int, Int, AEREQT, Bool) => Bool;
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

\* @type: (Int, MSG) => Bool;
ReturnToFollowerState(i, m) ==
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Candidate
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, history>>

\* @type: (Int, Int, Int, AEREQT) => Bool;
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

\* @type: (Int, Int, AEREQT) => Bool;
ConflictAppendEntriesRequest(i, index, m) ==
    /\ m.mentries /= << >>
    /\ Len(log[i]) >= index
    /\ log[i][index].term /= m.mentries[1].term
    \* /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |-> log[i][index2]]
    /\ LET new == SubSeq(log[i], 1, Len(log[i]) - 1)
       IN log' = [log EXCEPT ![i] = new]
    /\ UNCHANGED <<serverVars, commitIndex, messages, history>>

\* @type: (Int, AEREQT) => Bool;
NoConflictAppendEntriesRequest(i, m) ==
    /\ m.mentries /= << >>
    /\ Len(log[i]) = m.mprevLogIndex
    /\ log' = [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
    /\ UNCHANGED <<serverVars, commitIndex, messages, history>>

\* @type: (Int, Int, Bool, AEREQT) => Bool;
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
\* @type: (Int, Int, AEREQT) => Bool;
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
\* @type: (Int, Int, AERESPT) => Bool;
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
\* @type: (Int, Int, MSG) => Bool;
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, history>>

\* Responses with stale terms are ignored.
\* @type: (Int, Int, MSG) => Bool;
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Receive a message.
\* @type: MSG => Bool;
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
    \/ UpdateTerm(i, j, m)
    \/  /\ m.mtype = RequestVoteRequest
        /\ HandleRequestVoteRequest(i, j, m.RVReq)
    \/  /\ m.mtype = RequestVoteResponse
        /\  \/ DropStaleResponse(i, j, m.RVResp)
            \/ HandleRequestVoteResponse(i, j, m.RVResp)
    \/  /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(i, j, m.AEReq)
    \/  /\ m.mtype = AppendEntriesResponse
        /\  \/ DropStaleResponse(i, j, m.AEResp)
            \/ HandleAppendEntriesResponse(i, j, m.AEResp)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
\* @type: MSG => Bool;
DuplicateMessage(m) ==
    /\ SendWithoutHistory(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, history>>

\* The network drops a message
\* @type: MSG => Bool;
DropMessage(m) ==
    /\ DiscardWithoutHistory(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, history>>

----
\* Defines how the variables may transition.
Next == \/ \E i \in Server : Restart(i)
        \/ \E i \in Server : Timeout(i)
        \/ \E i,j \in Server : RequestVote(i, j)
        \/ \E i \in Server : BecomeLeader(i)
        \/ \E i \in Server, v \in Value : ClientRequest(i, v)
        \/ \E i \in Server : AdvanceCommitIndex(i)
        \/ \E i,j \in Server : AppendEntries(i, j)
        \/ \E m \in DOMAIN messages :
            Receive(m)
        \* Only duplicate once
        \/ \E m \in DOMAIN messages : 
            /\ messages[m] = 1
            /\ DuplicateMessage(m)
        \* Only drop if it makes a difference
        \/ \E m \in DOMAIN messages : 
            /\ messages[m] = 1
            /\ DropMessage(m)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The main safety properties are below                                    *)
(***************************************************************************)
----

ASSUME DistinctRoles == /\ Leader /= Candidate
                        /\ Candidate /= Follower
                        /\ Follower /= Leader

ASSUME DistinctMessageTypes == /\ RequestVoteRequest /= AppendEntriesRequest
                               /\ RequestVoteRequest /= RequestVoteResponse
                               /\ RequestVoteRequest /= AppendEntriesResponse
                               /\ AppendEntriesRequest /= RequestVoteResponse
                               /\ AppendEntriesRequest /= AppendEntriesResponse
                               /\ RequestVoteResponse /= AppendEntriesResponse

----
\* Correctness invariants

\* The prefix of the log of server i that has been committed
Committed(i) == SubSeq(log[i],1,commitIndex[i])

\* The current term of any server is at least the term
\* of any message sent by that server
\* @type: MSG => Bool;
MessageTermsLtCurrentTerm(m) ==
    m.mterm <= currentTerm[m.msource]

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

THEOREM ElectionsCorrect == Spec => [](CandidateTermNotInLog /\ LeaderVotesQuorum)

\* A leader always has the greatest index for its current term
ElectionSafety ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server :
            \* Max does not work on empty sets
            (/\ DOMAIN log[i] /= {}
             /\ DOMAIN log[j] /= {}) =>
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

-----

\* Constraints to make model checking more feasible

BoundedInFlightMessages == BagCardinality(messages) <= MaxInFlightMessages

BoundedLogSize == \A i \in Server: Len(log[i]) <= MaxLogLength

BoundedRestarts == \A i \in Server: history["server"][i]["restarted"] <= MaxRestarts

BoundedTimeouts == \A i \in Server: history["server"][i]["timeout"] <= MaxTimeouts

ElectionsUncontested == Cardinality({c \in DOMAIN state : state[c] = Candidate}) <= 1

CleanFirstLeaderElection ==
    (~ history["hadAtLeastOneLeader"]) =>
    /\ \A i \in Server: history["server"][i]["restarted"] = 0
    /\ \A i \in Server: history["server"][i]["restarted"] <= 1
    /\ ElectionsUncontested

-----

\* Generate interesting traces

BoundedTrace == Len(history["global"]) <= 12

FirstBecomeLeader == ~ \E i, j \in DOMAIN history["global"] :
    /\ i /= j
    /\ LET x == history["global"][i]
           y == history["global"][j] IN
        x.action = "Receive" /\ x.msg.mtype = RequestVoteResponse
        /\ y.action = "Receive" /\ y.msg.mtype = RequestVoteResponse
        /\ x.msg.msource /= y.msg.msource
        /\ state[x.msg.mdest] = Leader


===============================================================================

\* Changelog:
\* 
\* 2021-04-09:
\* - Added type annotations for Apalache symbolic model checker. As part of
\*   this change, the message format was changed to a tagged union.
\* 
\* 2016-09-09:
\* - Daniel Ricketts added the major safety invariants and proved them in
\*   TLAPS.
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
