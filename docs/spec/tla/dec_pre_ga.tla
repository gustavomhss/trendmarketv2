---- MODULE dec_pre_ga ----
EXTENDS Naturals, Sequences, TLC

VARIABLES dec_p95, breach, rollback, recovered

Init ==
    /\ dec_p95 \in Nat
    /\ dec_p95 = 0
    /\ breach = FALSE
    /\ rollback = FALSE
    /\ recovered = FALSE

MeasureBreached ==
    /\ dec_p95' \in Nat
    /\ dec_p95' > 800
    /\ breach' = TRUE
    /\ UNCHANGED <<rollback, recovered>>

RollbackIssued ==
    /\ breach = TRUE
    /\ rollback' = TRUE
    /\ UNCHANGED <<dec_p95, recovered>>

RecoveredWithinBudget ==
    /\ rollback = TRUE
    /\ dec_p95' \in Nat
    /\ dec_p95' <= 800
    /\ recovered' = TRUE
    /\ UNCHANGED <<breach>>

Stutter ==
    /\ dec_p95' = dec_p95
    /\ breach' = breach
    /\ rollback' = rollback
    /\ recovered' = recovered

Next == MeasureBreached \/ RollbackIssued \/ RecoveredWithinBudget \/ Stutter

Spec == Init /\ [][Next]_<<dec_p95, breach, rollback, recovered>>

Safety == [](breach => dec_p95 <= 1600)

Liveness == WF_<<dec_p95, breach, rollback, recovered>>(RollbackIssued) /\
            WF_<<dec_p95, breach, rollback, recovered>>(RecoveredWithinBudget)

THEOREM Spec => Safety
THEOREM Spec => <>RecoveredWithinBudget

====
