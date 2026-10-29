# Resource Locks and Fast Unlock: TLA+ Model

TLA+ specification of a certificate-based payment protocol in which several accounts can
debit one shared resource without consensus. The protocol has three parts:

- **Personal path.** Client-driven certificates, as in FastPay.
- **Shared path.** A transaction is sent to any validator. It is admitted only if both the
  sender nonce and the resource nonce are free. It is then certified by an `ECHO` / `READY`
  broadcast.
- **Fast unlock.** A stuck resource slot is frozen and resolved by validated agreement on
  that slot only.

This model accompanies the paper *Shared Resources without Consensus: Resource Locks and
Fast Unlock for Certificate-Based Payment Systems* (Lingkang Shangguan).

## Files

| File | Purpose |
|---|---|
| `ResourceLock.tla` | The specification and the safety invariants |
| `MC.tla` | Model-checking wrapper that declares the validator model values |
| `MC.cfg` | The protocol as designed (`UseReady = TRUE`); expected to pass |
| `MC_NoReady.cfg` | Finality at a bare echo quorum (`UseReady = FALSE`); expected to fail |
| `run.sh` | Downloads `tla2tools.jar` if needed and runs both checks |

## Model

- **Validators.** n = 4: honest `h1`, `h2`, `h3` and Byzantine `b` (f = 1). The Byzantine
  validator signs every message for every transaction, publicly or privately, and in a freeze
  set it may claim any echo quorum that exists.
- **Transactions.**
  - `A` and `B` are shared transactions from different accounts that race on resource `r1`.
  - `P` is a personal transaction with the same sender nonce as `A`, so the account
    equivocates across the two paths.
  - `C` is a shared transaction on `r2` with the same sender nonce as `A`, so it reuses the
    nonce after `A` loses.
- **Abstractions.** Any honest validator may freeze any slot at any time, which
  over-approximates the timeout, split and amplification triggers. Validated agreement is
  modeled as one atomic decision `Select(F)` over some valid freeze set `F`.

## Properties (`Safety`)

| Invariant | Meaning |
|---|---|
| `Consistency` | No two executed transactions share a nonce slot or a resource slot. |
| `FinalitySafe` | No executed transaction conflicts with a final one. |
| `UnlockRespectsFinal` | An unlock never decides against a final transaction. |
| `DeadNeverFinal` | A transaction marked dead never becomes final. |
| `UniqueQuorumPerSlot` | Each resource slot has at most one echo quorum. |

## Results

| Config | Distinct states | Result |
|---|---|---|
| `MC.cfg` | 41,333,964 (depth 30) | No error; the search is exhaustive (about 6 min on a laptop) |
| `MC_NoReady.cfg` | — | `Safety` violated at depth 6 |

The `MC_NoReady.cfg` counterexample runs as follows. `h1` and `h2` echo `A`. Together with
`b`'s private signature that is a quorum, so `A` is final. `h1` freezes before it stores the
quorum, and the unlock decides ⊥, which contradicts `A`. This shows why the `READY` phase is
needed.

## Running

Requires Java 11 or later.

```sh
./run.sh
```

To run one config by hand:

```sh
java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -workers auto -deadlock -config MC.cfg MC.tla
```

`-deadlock` turns off TLC's deadlock check. The model reaches terminal states once every
slot is resolved, and those states are not errors.

## Scope

Model checking covers this instance exhaustively, but not every committee size or workload.
The general case is proved in the paper. Reconfiguration and liveness are not modeled yet.
