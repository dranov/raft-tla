--------------------------------- MODULE raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro, 2015 Brandon Amos and Huanchen Zhang,
\* 2016 Daniel Ricketts, 2021 George Pîrlea.
\*
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, Integers, TypedBags, FiniteSets, Sequences, SequencesExt, TLC

\* The initial and global set of server IDs.
CONSTANTS InitServer, Server

\* The number of rounds to catch new servers up for.
\* Must be >= 1.
CONSTANT NumRounds

\* Log metadata to distinguish values from configuration changes.
CONSTANT ValueEntry, ConfigEntry

\* Constraints
MaxLogLength == 5
MaxRestarts == 2
MaxTimeouts == 3
MaxClientRequests == 3
MaxTerms == MaxTimeouts + 1
MaxMembershipChanges == 3
MaxTriedMembershipChanges == MaxMembershipChanges + 1
MaxInFlightMessages == LET card == Cardinality(Server) IN 2 * card * card

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
    AppendEntriesResponse,

    \* Membership changes
    CatchupRequest,
    CatchupResponse,
    CheckOldConfig

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
    \* @type: [server: Int -> [restarted: Int, timeout: Int], global: Seq(ACTION), hadNumLeaders: Int, hadNumClientRequests: Int];
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
systemState == [
    messages |-> messages,
    \* serverVars
    currentTerm |-> currentTerm,
    state |-> state,
    votedFor |-> votedFor,
    \* candidateVars
    votesResponded |-> votesResponded,
    votesGranted |-> votesGranted,
    \* leaderVars
    nextIndex |-> nextIndex,
    matchIndex |-> matchIndex,
    \* logVars
    log |-> log,
    commitIndex |-> commitIndex
]


----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum(config) == {i \in SUBSET(config) : Cardinality(i) * 2 > Cardinality(config)}

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
SendDirect(m) == 
    LET msgAction == [action |-> "Send", executedOn |-> m.msource, msg |-> m]
        membershipAction == 
        IF m.mtype = CatchupRequest
            THEN [action |-> "TryAddServer", executedOn |-> m.msource, added |-> m.mdest]
        ELSE IF m.mtype = CheckOldConfig
            THEN [action |-> "TryRemoveServer", executedOn |-> m.msource, removed |-> m.mserver]
        ELSE << >>
    IN
    /\ messages'    = WithMessage(m, messages)
    /\ history' =
        IF membershipAction = << >>
        THEN [history EXCEPT !["global"] = Append(history["global"], msgAction)]
        ELSE 
        [history EXCEPT 
            !["hadNumTriedMembershipChanges"] = history["hadNumTriedMembershipChanges"] + 1,
            !["global"] = Append(Append(history["global"], membershipAction), msgAction)]

\* @type: [msource: Int] => Bool;
SendWrapped(m) == 
    LET w == WrapMsg(m) IN
    SendDirect(w)

\* Used by the environment to duplicate messges.
SendWithoutHistoryDirect(m) == 
    messages' = WithMessage(m, messages)

\* @type: [msource: Int] => Bool;
SendWithoutHistoryWrapped(m) == 
    LET w == WrapMsg(m) IN
    SendWithoutHistoryDirect(w)

\* Remove a message from the bag of messages. Used when a server is done
DiscardDirect(m) ==
    LET action == [action |-> "Receive", executedOn |-> m.mdest, msg |-> m] IN
    /\ messages'    = WithoutMessage(m, messages)
    /\ history'     = [history EXCEPT !["global"] = Append(history["global"], action)]

DiscardDirectWithMembershipChange(m, extraAction) ==
    LET action == [action |-> "Receive", executedOn |-> m.mdest, msg |-> m] IN
    /\ messages'    = WithoutMessage(m, messages)
    /\ history'     = [history EXCEPT
            !["hadNumMembershipChanges"] = history["hadNumMembershipChanges"] + 1,
            !["global"] = Append(Append(history["global"], action), extraAction)]

\* processing a message.
\* @type: [mdest: Int] => Bool;
DiscardWrapped(m) ==
    LET w == WrapMsg(m) IN
    DiscardDirect(w)

\* Used by the environment to drop messges.
DiscardWithoutHistoryDirect(m) ==
    messages' = WithoutMessage(m, messages)

\* @type: a => Bool;
DiscardWithoutHistoryWrapped(m) ==
    LET w == WrapMsg(m) IN
    DiscardWithoutHistoryDirect(w)

\* Combination of Send and Discard
ReplyDirect(response, request) ==
    LET req == request IN
    LET resp == response IN
    LET recvA == [action |-> "Receive", executedOn |-> request.mdest, msg |-> req] IN
    LET respA == [action |-> "Send", executedOn |-> response.msource, msg |-> resp] IN
    /\ messages'    = WithoutMessage(req, WithMessage(resp, messages))
    /\ history'     = [history EXCEPT !["global"] = Append(Append(history["global"], recvA), respA)]

\* @type: ([msource: Int], [mdest: Int]) => Bool;
ReplyWrapped(response, request) ==
    LET wresp == WrapMsg(response) IN
    LET wreq == WrapMsg(request) IN
    ReplyDirect(wresp, wreq)

\* Default: change when needed
 Send(m) == SendDirect(m)
 Reply(response, request) == ReplyDirect(response, request)
 Discard(m) == DiscardDirect(m)
 DiscardWithMembershipChange(m, extraAction) == DiscardDirectWithMembershipChange(m, extraAction)
 SendWithoutHistory(m) == SendWithoutHistoryDirect(m)
 DiscardWithoutHistory(m) == DiscardWithoutHistoryDirect(m) 

\*Send(m) == SendWrapped(m)
\*Reply(response, request) == ReplyWrapped(response, request)
\*Discard(m) == DiscardWrapped(m)
\*SendWithoutHistory(m) == SendWithoutHistoryWrapped(m)
\*DiscardWithoutHistory(m) == DiscardWithoutHistoryWrapped(m) 

\* Return the minimum value from a set, or undefined if the set is empty.
\* @type: Set(Int) => Int;
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
\* @type: Set(Int) => Int;
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

MaxOrZero(s) == IF s = {} THEN 0 ELSE Max(s)

\* Return the index of the latest configuration in server i's log.
GetHistoricalMaxConfigIndex(i, s) ==
    LET configIndexes == { index \in 1..Len(s.log[i]) : s.log[i][index].type = ConfigEntry }
    IN IF configIndexes = {} THEN 0
       ELSE Max(configIndexes)

GetMaxConfigIndex(i) == GetHistoricalMaxConfigIndex(i, systemState)

\* Return the latest configuration in server i's log.
GetHistoricalConfig(i, s) ==
  LET maxConfigIndex == GetHistoricalMaxConfigIndex(i, s) IN
  IF maxConfigIndex = 0 THEN InitServer
  ELSE s.log[i][maxConfigIndex].value


GetConfig(i) == GetHistoricalConfig(i, systemState)

CurrentLeaders == {i \in Server : state[i] = Leader}

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
    hadNumLeaders |-> 0,
    hadNumClientRequests |-> 0,
    hadNumTriedMembershipChanges |-> 0,
    hadNumMembershipChanges |-> 0
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
              /\ i \in GetConfig(i)
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
    /\ j \in (GetConfig(i) \ votesResponded[i])
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
    /\ j \in GetConfig(i)
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
    /\ votesGranted[i] \in Quorum(GetConfig(i))
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ history'    = [history EXCEPT 
                            !["hadNumLeaders"] = history["hadNumLeaders"] + 1,
                            !["global"] = Append(history["global"], 
                                [action |-> "BecomeLeader", executedOn |-> i, leaders |-> (CurrentLeaders \cup {i})])]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars>>
    
\* Leader i receives a client request to add v to the log.
\* @type: (Int, Int) => Bool;
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ LET entry == [term  |-> currentTerm[i],
                     type  |-> ValueEntry,
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ history'    = [history EXCEPT !["hadNumClientRequests"] = history["hadNumClientRequests"] + 1]
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
\* @type: Int => Bool;
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in GetConfig(i) :
                                         matchIndex[i][k] >= index}
           logSize == Len(log[i])
           \* logSize == MaxLogLength
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..logSize :
                                Agree(index) \in Quorum(GetConfig(i))}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
            committed == newCommitIndex > commitIndex[i]
            committedMembershipChange ==
                /\ committed
                /\ log[i][newCommitIndex].type = ConfigEntry
                \* The newly commited entry actually changes the configuration, i.e. is not the same config commited again
                /\ log[i][newCommitIndex].value /= 
                    GetHistoricalConfig(i, [log |-> [log EXCEPT ![i] = SubSeq(log[i], 1, newCommitIndex - 1)]])
       IN
        /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
        /\ IF committedMembershipChange THEN 
            history' = [history EXCEPT
                !["global"] = Append(history["global"],
                    [action |-> "CommitMembershipChange", executedOn |-> i, config |-> log[i][newCommitIndex].value])]
            ELSE IF committed THEN
             history' = [history EXCEPT
                !["global"] = Append(history["global"], [action |-> "CommitEntry", executedOn |-> i, entry |-> log[i][newCommitIndex]])]
            ELSE UNCHANGED <<history>>
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log>>

\* Leader i adds a new server j to the cluster.
AddNewServer(i, j) ==
    /\ state[i] = Leader
    /\ j \notin GetConfig(i)
    /\ currentTerm' = [currentTerm EXCEPT ![j] = 1]
    /\ votedFor' = [votedFor EXCEPT ![j] = Nil]
    /\ Send([mtype |-> CatchupRequest,
            mterm |-> currentTerm[i],
            mlogLen |-> matchIndex[i][j],
            mentries |-> SubSeq(log[i], nextIndex[i][j], commitIndex[i]),
            mcommitIndex |-> commitIndex[i],
            msource |-> i,
            mdest |-> j,
            mrounds |-> NumRounds])
    /\ UNCHANGED <<state, leaderVars, logVars, candidateVars>>

\* Leader i removes a server j (possibly itself) from the cluster.
DeleteServer(i, j) ==
    /\ state[i] = Leader
    /\ state[j] \in {Follower, Candidate}
    /\ j \in GetConfig(i)
    /\ j /= i \* TODO: A leader cannot remove itself.
    /\ Send([mtype |-> CheckOldConfig,
            mterm |-> currentTerm[i],
            madd |-> FALSE,
            mserver |-> j,
            msource |-> i,
            mdest |-> i])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

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
    /\ UNCHANGED <<serverVars, log>>

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
    IN 
       /\ m.mterm <= currentTerm[i]
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

\* Detached server i receives a CatchupRequest from leader j.
HandleCatchupRequest(i, j, m) ==
  \/ /\ m.mterm < currentTerm[i]
     /\ Reply([mtype |-> CatchupResponse,
               mterm |-> currentTerm[i],
               msuccess |-> FALSE,
               mmatchIndex |-> 0,
               msource |-> i,
               mdest |-> j,
               mroundsLeft |-> 0],
               m)
     /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
  \/ /\ m.mterm >= currentTerm[i]
     /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
    \* This was previously the following, but that's buggy
    \* (shows how this spec wasn't tested very extensively)
    \* /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, m.mlogLen) \circ m.mentries]
     /\ log' = [log EXCEPT ![i] =
            IF log[i] = << >> THEN m.mentries
            ELSE SubSeq(log[i], 1, Min({m.mlogLen, Len(log[i])})) \circ m.mentries]
     /\ Reply([mtype |-> CatchupResponse,
               mterm |-> m.mterm,
               msuccess |-> TRUE,
               mmatchIndex |-> Len(log[i]),
               msource |-> i,
               mdest |-> j,
               mroundsLeft |-> m.mrounds - 1],
              m)
     /\ UNCHANGED <<state, votedFor, candidateVars, leaderVars, commitIndex>>

\* Leader i receives a CatchupResponse from detached server j.
HandleCatchupResponse(i, j, m) ==
  \* A real system checks for progress every timeout interval.
  \* Assume that if this response is called, the new server
  \* has made progress.
  /\ \/ /\ m.msuccess
        /\ \/ /\ m.mmatchIndex /= commitIndex[i]
              /\ m.mmatchIndex /= matchIndex[i][j]
           \/ m.mmatchIndex = commitIndex[i]
        /\ state[i] = Leader
        /\ m.mterm = currentTerm[i]
        /\ j \notin GetConfig(i)
        /\ nextIndex' = [nextIndex EXCEPT ![i][j] = m.mmatchIndex + 1]
        /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
        /\ \/ /\ m.mroundsLeft /= 0
              /\ Reply([mtype |-> CatchupRequest,
                        mterm |-> currentTerm[i],
                        mentries |-> SubSeq(log[i],
                                            nextIndex[i][j],
                                            commitIndex[i]),
                        mlogLen |-> nextIndex[i][j] - 1,
                        msource |-> i,
                        mdest |-> j,
                        mrounds |-> m.mroundsLeft],
                        m)
           \/ /\ m.mroundsLeft = 0
              \* A real system makes sure the final call to this handler is
              \* received after a timeout interval.
              \* We assume that if a timeout happened, the message
              \* has already been dropped.
              /\ Reply([mtype |-> CheckOldConfig,
                       mterm |-> currentTerm[i],
                       madd |-> TRUE,
                       mserver |-> j,
                       msource |-> i,
                       mdest |-> i], m)
     \/ /\ \/ \lnot m.msuccess
           \/ /\ \/ m.mmatchIndex = commitIndex[i]
                 \/ m.mmatchIndex = matchIndex[i][j]
              /\ m.mmatchIndex /= commitIndex[i]
           \/ state[i] /= Leader
           \/ m.mterm /= currentTerm[i]
           \/ j \in GetConfig(i)
        /\ Discard(m)
        /\ UNCHANGED <<leaderVars>>
  /\ UNCHANGED <<serverVars, candidateVars, logVars>>

\* Leader i receives a CheckOldConfig message.
HandleCheckOldConfig(i, m) ==
  \/ /\ state[i] /= Leader \/ m.mterm = currentTerm[i]
     /\ Discard(m)
     /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
  \/ /\ state[i] = Leader /\ m.mterm = currentTerm[i]
     /\ \/ /\ GetMaxConfigIndex(i) <= commitIndex[i]
            \* We only modify the log if the config actually changed
           /\ LET action == IF m.madd THEN [action |-> "AddServer", executedOn |->i, added |-> m.mserver]
                            ELSE [action |-> "RemoveServer", executedOn |-> i, removed |-> m.mserver]
                  newConfig == IF m.madd THEN UNION { GetConfig(i), {m.mserver} }
                               ELSE GetConfig(i) \ {m.mserver}
                  configChanged == GetConfig(i) /= newConfig
                  newEntry == [term |-> currentTerm[i], type |-> ConfigEntry, value |-> newConfig]
                  newLog == IF configChanged THEN Append(log[i], newEntry) ELSE log[i]
              IN 
              /\ log' = [log EXCEPT ![i] = newLog]
              /\ IF configChanged THEN DiscardWithMembershipChange(m, action) ELSE Discard(m)
            /\ UNCHANGED <<commitIndex>>
        \/ /\ GetMaxConfigIndex(i) > commitIndex[i]
           /\ Reply([mtype |-> CheckOldConfig,
                     mterm |-> currentTerm[i],
                     madd |-> m.madd,
                     mserver |-> m.mserver,
                     msource |-> i,
                     mdest |-> i],
                     m)
           /\ UNCHANGED <<logVars>>
     /\ UNCHANGED <<serverVars, candidateVars, leaderVars>>
    
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
ReceiveDirect(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
    \/ UpdateTerm(i, j, m)
    \/  /\ m.mtype = RequestVoteRequest
        /\ HandleRequestVoteRequest(i, j, m)
    \/  /\ m.mtype = RequestVoteResponse
        /\  \/ DropStaleResponse(i, j, m)
            \/ HandleRequestVoteResponse(i, j, m)
    \/  /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(i, j, m)
    \/  /\ m.mtype = AppendEntriesResponse
        /\  \/ DropStaleResponse(i, j, m)
            \/ HandleAppendEntriesResponse(i, j, m)
    \/  /\ m.mtype = CatchupRequest
        /\ HandleCatchupRequest(i, j, m)
    \/  /\ m.mtype = CatchupResponse
        /\ HandleCatchupResponse(i, j, m)
    \/  /\ m.mtype = CheckOldConfig
        /\ HandleCheckOldConfig(i, m)

\* @type: MSG => Bool;
ReceiveWrapped(m) ==
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

 Receive(m) == ReceiveDirect(m)
\*Receive(m) == ReceiveWrapped(m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
\* @type: MSG => Bool;
DuplicateMessage(m) ==
    \* Do not duplicate loopback messages
    \* /\ m.msource /= m.mdest
    /\ SendWithoutHistory(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, history>>

\* The network drops a message
\* @type: MSG => Bool;
DropMessage(m) ==
    \* Do not drop loopback messages
    \* /\ m.msource /= m.mdest
    /\ DiscardWithoutHistory(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, history>>

----

\* Defines how the variables may transition.
NextAsync == 
    \/ \E i,j \in Server : RequestVote(i, j)
    \/ \E i \in Server : BecomeLeader(i)
    \/ \E i \in Server, v \in Value : ClientRequest(i, v)
    \/ \E i \in Server : AdvanceCommitIndex(i)
    \/ \E i,j \in Server : AppendEntries(i, j)
    \/ \E m \in DOMAIN messages : Receive(m)
    \/ \E i \in Server : Timeout(i)
        
NextCrash == \E i \in Server : Restart(i)

NextAsyncCrash ==
    \/ NextAsync
    \/ NextCrash

NextUnreliable ==    
    \* Only duplicate once
    \/ \E m \in DOMAIN messages : 
        /\ messages[m] = 1
        /\ DuplicateMessage(m)
    \* Only drop if it makes a difference            
    \/ \E m \in DOMAIN messages : 
        /\ messages[m] = 1
        /\ DropMessage(m)

\* Most pessimistic network model
Next == \/ NextAsync
        \/ NextCrash
        \/ NextUnreliable

\* Membership changes
NextDynamic ==
    \/ Next
    \/ \E i, j \in Server : AddNewServer(i, j)
    \/ \E i, j \in Server : DeleteServer(i, j)

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
    
\* NOTE: this only makes sense if there are no configuration changes
\* All leaders have a quorum of servers who either voted
\* for the leader or have a higher term
LeaderVotesQuorum ==
    history["hadNumMembershipChanges"] = 0 =>
    \A i \in Server :
        state[i] = Leader =>
        {j \in Server : currentTerm[j] > currentTerm[i] \/
                        (currentTerm[j] = currentTerm[i] /\ votedFor[j] = i)} \in Quorum(GetConfig(i))

\* If a candidate has a chance of being elected, there
\* are no log entries with that candidate's term
CandidateTermNotInLog ==
    history["hadNumMembershipChanges"] = 0 =>
    \A i \in Server :
        (/\ state[i] = Candidate
         /\ {j \in Server : currentTerm[j] = currentTerm[i] /\ votedFor[j] \in {i, Nil}} \in Quorum(GetConfig(i))) =>
        \A j \in Server :
        \A n \in DOMAIN log[j] :
             log[j][n].term /= currentTerm[i]

THEOREM ElectionsCorrect == Spec => [](CandidateTermNotInLog /\ LeaderVotesQuorum)

\* A leader always has the greatest index for its current term
ElectionSafety ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server :
            MaxOrZero({n \in DOMAIN log[i] : log[i][n].term = currentTerm[i]}) >=
            MaxOrZero({n \in DOMAIN log[j] : log[j][n].term = currentTerm[i]})
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

\* This property, written by Daniel Ricketts, is in fact
\* violated. This suggests the spec was not model-checked
\* extensively.

\* The English description is correct, but the TLA
\* does NOT match it due to a confusion about the meaning
\* of the spec variables.

\* Votes are only granted to servers with logs
\* that are at least as up to date
VotesGrantedInv_false ==
    \A i \in Server :
    \A j \in votesGranted[i] :
        currentTerm[i] = currentTerm[j] =>
        \* The following is a subtlety:
        \* Only the committed entries of j are
        \* a prefix of i's log, not the entire 
        \* log of j
        IsPrefix(Committed(j),log[i])

VotesGrantedInv ==
    \A i, j \in Server :
        \* if i has voted for j
        votedFor[i] = j =>
            IsPrefix(Committed(i), log[j])

\* All committed entries are contained in the log
\* of at least one server in every quorum
QuorumLogInv ==
    \A i \in Server :
    \A S \in Quorum(GetConfig(i)) :
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

\* This property, written by Daniel Rickett's, is in fact
\* violated by the spec (when there are multiple concurrent leaders).
\* This suggests the spec was not model-checked extensively.

\* The committed entries in every log are a prefix of the
\* leader's log
LeaderCompleteness_false ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server :
            IsPrefix(Committed(j),log[i])

\* If a log entry is committed in a given term, then that
\* entry will be present in the logs of the leaders
\* for all higher-numbered terms
\* See: https://github.com/uwplse/verdi-raft/blob/master/raft/LeaderCompletenessInterface.v
LeaderCompleteness == 
    \A i \in Server :
        LET committed == Committed(i) IN
        \A idx \in 1..Len(committed) :
            LET entry == log[i][idx] IN 
            \* if the entry is committed 
            \A l \in CurrentLeaders :
                \* all leaders with higher-number terms
                currentTerm[l] > entry.term =>
                \* have the entry at the same log position
                log[l][idx] = entry

-----

\* Constraints to make model checking more feasible

BoundedInFlightMessages == BagCardinality(messages) <= MaxInFlightMessages

\* The spec allows for a candidate to send as many RequestVote messages as they want
BoundedRequestVote ==
    \A m \in DOMAIN messages:
        m.mtype = RequestVoteRequest => messages[m] <= 1

BoundedLogSize == \A i \in Server: Len(log[i]) <= MaxLogLength

BoundedRestarts == \A i \in Server: history["server"][i]["restarted"] <= MaxRestarts

BoundedTimeouts == \A i \in Server: history["server"][i]["timeout"] <= MaxTimeouts

BoundedTerms == \A i \in Server: currentTerm[i] <= MaxTerms

BoundedClientRequests == history["hadNumClientRequests"] <= MaxClientRequests

BoundedTriedMembershipChanges == history["hadNumTriedMembershipChanges"] <= MaxTriedMembershipChanges

BoundedMembershipChanges == history["hadNumMembershipChanges"] <= MaxMembershipChanges

ElectionsUncontested == Cardinality({c \in DOMAIN state : state[c] = Candidate}) <= 1

CleanStartUntilFirstRequest ==
    ((history["hadNumLeaders"] < 1 /\ history["hadNumClientRequests"] < 1)) =>
    /\ \A i \in Server: history["server"][i]["restarted"] = 0
    /\ Sum([i \in Server |-> history["server"][i]["timeout"]]) <= 1        
    /\ ElectionsUncontested

CleanStartUntilTwoLeaders ==
    (history["hadNumLeaders"] < 2) =>
    /\ Sum([i \in Server |-> history["server"][i]["restarted"]]) <= 1      
    /\ Sum([i \in Server |-> history["server"][i]["timeout"]]) <= 2        

-----

\* Generate interesting traces

BoundedTrace == Len(history["global"]) <= 24

FirstBecomeLeader == ~ \E i \in DOMAIN history["global"] :
    history["global"][i].action = "BecomeLeader"

FirstCommit == ~ \E i \in Server : commitIndex[i] > 0

FirstRestart == ~ \E i \in Server : history["server"][i]["restarted"] >= 2

LeadershipChange == history["hadNumLeaders"] < 2

MembershipChange == history["hadNumMembershipChanges"] < 1

MultipleMembershipChanges == history["hadNumMembershipChanges"] < 2

ConcurrentLeaders == ~ (Cardinality(CurrentLeaders) >= 2)

EntryCommitted == ~
    \E i \in DOMAIN history["global"] :
    /\ LET x == history["global"][i] IN
        /\ x.action = "CommitEntry"

CommitWhenConcurrentLeaders == ~
    \E i, k \in DOMAIN history["global"] :
    /\ i < k
    /\ LET  x == history["global"][i]
            y == history["global"][k]
        IN
        /\ x.action = "BecomeLeader" /\ Cardinality(x.leaders) >= 2
        /\ y.action = "CommitEntry"
    \* Run for a few more steps
    /\ Len(history["global"]) >= k + 2
    \* Still have concurrent leaders
    /\ Cardinality(CurrentLeaders) >= 2

\* A constraint to ease finding a violation of CommitWhenConcurrentLeaders:
\* the shortest trace (using NextAsync) where ConcurrentLeaders is vZiolated
\* has length 20, so we constrain the search space given the fact that
\* CommitWhenConcurrentLeaders implies ConcurrentLeaders held in the past.
CommitWhenConcurrentLeaders_constraint ==
    (Len(history["global"]) >= 20) =>
        \E i \in DOMAIN history["global"] :
            LET x == history["global"][i] IN
            x.action = "BecomeLeader" /\ Cardinality(x.leaders) >= 2

\* BUT, in fact, this does not get us a tremendous boost. When the trace gets
\* long enough, there are many ways to satisfy a particular constraint, so
\* you still get hit by state space explosion. For example, there are over 1.2 million
\*  traces of length 20 that satisfy CommitWhenConcurrentLeaders_constraint.
\* But we can use the fact that:
\*      CommitWhenConcurrentLeaders => ConcurrentLeaders on a prefix of the trace
\* to great effect! Concretely:
\* 
\* For any trace property P of the form Q /\ R, where Q and R are properties of a
\* (non-intersecting) trace prefix and suffix, respectively, we can run BFS to
\* find a trace that satisfies Q (let F_Q be the final state in such a trace), and
\* then run BFS again with F_Q as initial state to find a trace that satisfies R
\* and thus implicitly satisfies P.
CommitWhenConcurrentLeaders_unique ==
    \E s1, s2, s3 \in Server :
        /\ Cardinality({s1, s2, s3}) = 3
        /\ LET  ConcurrentLeaders_trace == [global |-> <<[action |-> "Timeout", executedOn |-> s1], [action |-> "Send", executedOn |-> s1, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s1, msg |-> [mdest |-> s1, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Receive", executedOn |-> s1, msg |-> [mdest |-> s1, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s1, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s2, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s1, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s2, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s1, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "BecomeLeader", executedOn |-> s1, leaders |-> {s1}], [action |-> "Timeout", executedOn |-> s2], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s3, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s3, msg |-> [mdest |-> s3, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s3, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s3, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s3, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "BecomeLeader", executedOn |-> s2, leaders |-> {s1, s2}]>>, hadNumClientRequests |-> 0, hadNumLeaders |-> 2, hadNumMembershipChanges |-> 0, hadNumTriedMembershipChanges |-> 0, server |-> (s1 :> [restarted |-> 0, timeout |-> 1] @@ s2 :> [restarted |-> 0, timeout |-> 1] @@ s3 :> [restarted |-> 0, timeout |-> 0])]
                maxLen == Min({Len(ConcurrentLeaders_trace["global"]), Len(history["global"])})
                prefix == SubSeq(ConcurrentLeaders_trace["global"], 1, maxLen)
            IN IsPrefix(prefix, history["global"])

\* We can also constrain the future via action constraints.
CommitWhenConcurrentLeaders_action_constraint ==
    (Len(history["global"]) >= 20) =>
        \* No timeouts
        /\ \A i \in Server : state'[i] /= Candidate

MajorityOfClusterRestarts == ~
    \* We want some non-trivial logs
    /\ \E i, j \in Server :
        /\ i /= j
        /\ Len(log[i]) >= 2
        /\ Len(log[j]) >= 1
    /\ \E maj \in Quorum(Server) :
        \A i \in maj: history["server"][i]["restarted"] >= 1
    \* There is activity between the restarts
    /\ \A i, k \in DOMAIN history["global"] :
        (
        /\ (i < k)
        /\ history["global"][i].action = "Restart"
        /\ history["global"][k].action = "Restart"
        ) => (k - i) >= 6

MajorityOfClusterRestarts_constraint ==
    \E s1, s2, s3 \in Server :
        /\ Cardinality({s1, s2, s3}) = 3
        /\ LET  CommitWhenConcurrentLeaders_trace == [global |-> <<[action |-> "Timeout", executedOn |-> s1], [action |-> "Send", executedOn |-> s1, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s1, msg |-> [mdest |-> s1, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Receive", executedOn |-> s1, msg |-> [mdest |-> s1, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s1, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s2, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s1, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s2, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s1, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "BecomeLeader", executedOn |-> s1, leaders |-> {s1}], [action |-> "Timeout", executedOn |-> s2], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s3, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s3, msg |-> [mdest |-> s3, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s3, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s3, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s3, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "BecomeLeader", executedOn |-> s2, leaders |-> {s1, s2}], [action |-> "Send", executedOn |-> s1, msg |-> [mcommitIndex |-> 0, mdest |-> s2, mentries |-> <<[term |-> 2, type |-> "ValueEntry", value |-> 1]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "AppendEntriesRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mcommitIndex |-> 0, mdest |-> s3, mentries |-> <<[term |-> 3, type |-> "ValueEntry", value |-> 2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "AppendEntriesRequest"]], [action |-> "Receive", executedOn |-> s3, msg |-> [mcommitIndex |-> 0, mdest |-> s3, mentries |-> <<[term |-> 3, type |-> "ValueEntry", value |-> 2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "AppendEntriesRequest"]], [action |-> "Send", executedOn |-> s3, msg |-> [mdest |-> s2, mmatchIndex |-> 1, msource |-> s3, msuccess |-> TRUE, mterm |-> 3, mtype |-> "AppendEntriesResponse"]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mmatchIndex |-> 1, msource |-> s3, msuccess |-> TRUE, mterm |-> 3, mtype |-> "AppendEntriesResponse"]], [action |-> "CommitEntry", entry |-> [term |-> 3, type |-> "ValueEntry", value |-> 2], executedOn |-> s2], [action |-> "Receive", executedOn |-> s2, msg |-> [mcommitIndex |-> 0, mdest |-> s2, mentries |-> <<[term |-> 2, type |-> "ValueEntry", value |-> 1]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "AppendEntriesRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s1, mmatchIndex |-> 0, msource |-> s2, msuccess |-> FALSE, mterm |-> 3, mtype |-> "AppendEntriesResponse"]]>>, hadNumClientRequests |-> 2, hadNumLeaders |-> 2, hadNumMembershipChanges |-> 0, hadNumTriedMembershipChanges |-> 0, server |-> (s1 :> [restarted |-> 0, timeout |-> 1] @@ s2 :> [restarted |-> 0, timeout |-> 1] @@ s3 :> [restarted |-> 0, timeout |-> 0])]
                maxLen == Min({Len(CommitWhenConcurrentLeaders_trace["global"]), Len(history["global"])})
                prefix == SubSeq(CommitWhenConcurrentLeaders_trace["global"], 1, maxLen)
            IN IsPrefix(prefix, history["global"])

AddSucessful == ~ \E i \in DOMAIN history["global"] :
    history["global"][i].action = "AddServer"

MembershipChangeCommits == ~ \E i \in DOMAIN history["global"] :
    history["global"][i].action = "CommitMembershipChange"

MultipleMembershipChangesCommit == ~
    \E i, j \in DOMAIN history["global"] :
    /\ i < j
    /\ history["global"][i].action = "CommitMembershipChange"
    /\ history["global"][j].action = "CommitMembershipChange"

AddCommits == ~
    \E i, j \in DOMAIN history["global"] :
    /\ i < j
    /\ LET  x == history["global"][i]
            y == history["global"][j]
        IN
        /\ x.action = "AddServer"
        /\ y.action = "CommitMembershipChange"
        /\ x.added \in y.config

NewlyJoinedBecomeLeader == ~
    \E i, j \in DOMAIN history["global"] :
    /\ i < j
    /\ LET  x == history["global"][i]
            y == history["global"][j]
        IN
        /\ x.action = "AddServer"
        /\ y.action = "BecomeLeader"
        /\ x.added = y.executedOn

LeaderChangesDuringConfChange == ~
    \E i, k \in DOMAIN history["global"] :
    /\ i < k
    /\ LET  x == history["global"][i]
            y == history["global"][k]
        IN
        /\ x.action = "AddServer"
        /\ y.action = "BecomeLeader"
    \* The membership change does not commit before the leader changes
    /\ ~ \E j \in i..k :
        /\ history["global"][j].action = "CommitMembershipChange"

\* Optimisations for TLC
perms == Permutations(Server)
\* vars is used as a view (we ignore history)

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
\* 2015-05-10:
\* - Add cluster membership changes as described in Section 4 of
\*     Diego Ongaro. Consensus: Bridging theory and practice.
\*     PhD thesis, Stanford University, 2014.
\*   This introduces: InitServer, ValueEntry, ConfigEntry, CatchupRequest,
\*     CatchupResponse, CheckOldConfig, GetMaxConfigIndex,
\*     GetConfig (parameterized), AddNewServer, DeleteServer,
\*     HandleCatchupRequest, HandleCatchupResponse,
\*     HandleCheckOldConfig 
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
