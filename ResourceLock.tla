---------------------------- MODULE ResourceLock ----------------------------
(***************************************************************************)
(* Resource locks and fast unlock for certificate-based payments.         *)
(*                                                                         *)
(* Personal transactions use client-driven certificates (FastPay).        *)
(* Shared transactions use ECHO / READY with dual-nonce admission, and a   *)
(* stuck resource slot is frozen and resolved by validated agreement,      *)
(* abstracted here as a single atomic decision over a valid freeze set.   *)
(*                                                                         *)
(* Byzantine validators are modeled as signing every message for every    *)
(* transaction, privately or publicly: they count towards every quorum,   *)
(* and in a freeze set they may claim any echo quorum that exists.        *)
(*                                                                         *)
(* UseReady = FALSE models finality at a bare echo quorum, which the      *)
(* paper shows to be unsafe once slots can be unlocked.                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Honest, Byz, UseReady

Validators == Honest \cup Byz
F == Cardinality(Byz)
Q == 2 * F + 1
ASSUME Cardinality(Validators) = 3 * F + 1

None == "none"
Pending == "pending"

\* Workload: every transaction uses nonce 1 of its sender.
\*   A, B : shared, different senders, race on resource r1
\*   P    : personal, same sender as A (nonce equivocation across paths)
\*   C    : shared on r2, same sender as A (nonce reuse after A loses)
Txs == {"A", "B", "P", "C"}
Accounts == {"a1", "a2"}
Resources == {"r1", "r2"}

Sender(t) == CASE t = "A" -> "a1" [] t = "B" -> "a2"
               [] t = "P" -> "a1" [] t = "C" -> "a1"
Res(t) == CASE t = "A" -> "r1" [] t = "B" -> "r1"
            [] t = "C" -> "r2" [] t = "P" -> None
Shared == {t \in Txs : Res(t) # None}
Personal == Txs \ Shared
OnRes(r) == {t \in Shared : Res(t) = r}

Conflict(t1, t2) ==
    /\ t1 # t2
    /\ \/ Sender(t1) = Sender(t2)
       \/ Res(t1) # None /\ Res(t1) = Res(t2)

VARIABLES
    lock,      \* lock[v][a]: transaction holding nonce slot of account a at v
    echoed,    \* echoed[v][r]: transaction v echoed on resource slot r
    pc,        \* pc[v][r]: transaction whose echo quorum v stored
    frozen,    \* frozen[v][r]
    echoes,    \* honest admissions (echoes / personal votes) as <<v, t>>
    readies,   \* honest READY messages as <<v, t>>
    decision,  \* decision[r]: Pending, None (released) or a transaction
    applied,   \* <<v, r>> pairs where v applied the decision
    dead,      \* dead[v]: transactions v knows lost
    executed   \* executed[v]

vars == <<lock, echoed, pc, frozen, echoes, readies, decision, applied,
          dead, executed>>

Support(t) == Cardinality({v \in Honest : <<v, t>> \in echoes}) + F
HasQuorum(t) == Support(t) >= Q
ReadySupport(t) == Cardinality({v \in Honest : <<v, t>> \in readies}) + F

Final(t) ==
    IF t \in Personal \/ ~UseReady THEN HasQuorum(t)
    ELSE ReadySupport(t) >= Q

Init ==
    /\ lock = [v \in Honest |-> [a \in Accounts |-> None]]
    /\ echoed = [v \in Honest |-> [r \in Resources |-> None]]
    /\ pc = [v \in Honest |-> [r \in Resources |-> None]]
    /\ frozen = [v \in Honest |-> [r \in Resources |-> FALSE]]
    /\ echoes = {}
    /\ readies = {}
    /\ decision = [r \in Resources |-> Pending]
    /\ applied = {}
    /\ dead = [v \in Honest |-> {}]
    /\ executed = [v \in Honest |-> {}]

\* Admission: user nonce free (or held by t) and, for shared, resource nonce free.
Admissible(v, t) ==
    /\ <<v, t>> \notin echoes
    /\ t \notin dead[v]
    /\ lock[v][Sender(t)] \in {None, t}
    /\ t \in Shared =>
           /\ echoed[v][Res(t)] = None
           /\ ~frozen[v][Res(t)]

Admit(v, t) ==
    /\ Admissible(v, t)
    /\ echoes' = echoes \cup {<<v, t>>}
    /\ lock' = [lock EXCEPT ![v][Sender(t)] = t]
    /\ echoed' = IF t \in Shared THEN [echoed EXCEPT ![v][Res(t)] = t]
                 ELSE echoed
    /\ UNCHANGED <<pc, frozen, readies, decision, applied, dead, executed>>

Ready(v, t) ==
    /\ t \in Shared
    /\ HasQuorum(t)
    /\ ~frozen[v][Res(t)]
    /\ <<v, t>> \notin readies
    /\ pc' = [pc EXCEPT ![v][Res(t)] = t]
    /\ readies' = readies \cup {<<v, t>>}
    /\ UNCHANGED <<lock, echoed, frozen, echoes, decision, applied, dead,
                   executed>>

Execute(v, t) ==
    /\ Final(t)
    /\ t \notin executed[v]
    /\ executed' = [executed EXCEPT ![v] = @ \cup {t}]
    /\ UNCHANGED <<lock, echoed, pc, frozen, echoes, readies, decision,
                   applied, dead>>

\* Triggers (timeout, split, amplification) only affect liveness, so a
\* validator may freeze any slot at any time.
Freeze(v, r) ==
    /\ ~frozen[v][r]
    /\ frozen' = [frozen EXCEPT ![v][r] = TRUE]
    /\ UNCHANGED <<lock, echoed, pc, echoes, readies, decision, applied,
                   dead, executed>>

\* Validated agreement on slot r: the decided value is Select(F) for some
\* freeze set F. Honest reports are fixed once frozen; Byzantine reports may
\* claim any echo quorum that exists.
ValidClaims(r) == {t \in OnRes(r) : HasQuorum(t)} \cup {None}

Decide(r) ==
    /\ decision[r] = Pending
    /\ \E S \in SUBSET Validators :
         /\ Cardinality(S) = Q
         /\ \A v \in S \cap Honest : frozen[v][r]
         /\ \E claim \in [S \cap Byz -> ValidClaims(r)] :
              LET pcs == ({pc[v][r] : v \in S \cap Honest}
                            \cup {claim[b] : b \in S \cap Byz}) \ {None}
              IN  \/ /\ pcs = {}
                     /\ decision' = [decision EXCEPT ![r] = None]
                  \/ \E t \in pcs :
                     decision' = [decision EXCEPT ![r] = t]
    /\ UNCHANGED <<lock, echoed, pc, frozen, echoes, readies, applied,
                   dead, executed>>

ApplyDecision(v, r) ==
    /\ decision[r] # Pending
    /\ <<v, r>> \notin applied
    /\ LET losers == OnRes(r) \ {decision[r]}
       IN  /\ dead' = [dead EXCEPT ![v] = @ \cup losers]
           /\ lock' = [lock EXCEPT ![v] =
                  [a \in Accounts |->
                     IF lock[v][a] \in losers THEN None ELSE lock[v][a]]]
    /\ executed' = IF decision[r] = None THEN executed
                   ELSE [executed EXCEPT ![v] = @ \cup {decision[r]}]
    /\ frozen' = [frozen EXCEPT ![v][r] = TRUE]
    /\ applied' = applied \cup {<<v, r>>}
    /\ UNCHANGED <<echoed, pc, echoes, readies, decision>>

Next ==
    \/ \E v \in Honest, t \in Txs : Admit(v, t) \/ Ready(v, t) \/ Execute(v, t)
    \/ \E v \in Honest, r \in Resources : Freeze(v, r) \/ ApplyDecision(v, r)
    \/ \E r \in Resources : Decide(r)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ lock \in [Honest -> [Accounts -> Txs \cup {None}]]
    /\ echoed \in [Honest -> [Resources -> Txs \cup {None}]]
    /\ pc \in [Honest -> [Resources -> Txs \cup {None}]]
    /\ decision \in [Resources -> Txs \cup {None, Pending}]

ExecutedAny == UNION {executed[v] : v \in Honest}

\* No two executed transactions share a nonce slot or a resource slot.
Consistency == \A t1, t2 \in ExecutedAny : ~Conflict(t1, t2)

\* A final transaction is never contradicted by an executed one.
FinalitySafe == \A t \in Txs : Final(t) =>
                    \A t2 \in ExecutedAny : ~Conflict(t, t2)

\* The unlock never decides against a final transaction (Lemma: Visibility).
UnlockRespectsFinal == \A t \in Shared :
                          Final(t) => decision[Res(t)] \in {Pending, t}

\* A transaction known dead is never final (Lemma: Dead transactions).
DeadNeverFinal == \A v \in Honest : \A t \in dead[v] : ~Final(t)

\* At most one echo quorum per resource slot (Lemma: Unique echo quorum).
UniqueQuorumPerSlot == \A r \in Resources : \A t1, t2 \in OnRes(r) :
                          (t1 # t2) => ~(HasQuorum(t1) /\ HasQuorum(t2))

Safety == /\ Consistency /\ FinalitySafe /\ UnlockRespectsFinal
          /\ DeadNeverFinal /\ UniqueQuorumPerSlot

=============================================================================
