---- MODULE dec_pre_ga ----
EXTENDS Naturals, TLC

\* Snowcat: uma anotação por variável (ASCII puro).
\* @type: dec_p95: Int;
\* @type: breach: Bool;
\* @type: rollback: Bool;
\* @type: recovered: Bool;
VARIABLES dec_p95, breach, rollback, recovered

vars == <<dec_p95, breach, rollback, recovered>>

TypeOK ==
    /\ dec_p95 \in Nat
    /\ breach \in BOOLEAN
    /\ rollback \in BOOLEAN
    /\ recovered \in BOOLEAN

Init ==
    /\ TypeOK
    /\ dec_p95 = 0
    /\ breach = FALSE
    /\ rollback = FALSE
    /\ recovered = FALSE

MeasureBreached ==
    /\ breach = FALSE
    /\ dec_p95' \in Nat
    /\ dec_p95' > 800
    /\ dec_p95' <= 1600
    /\ breach' = TRUE
    /\ UNCHANGED <<rollback, recovered>>

RollbackIssued ==
    /\ breach = TRUE
    /\ rollback' = TRUE
    /\ UNCHANGED <<dec_p95, recovered, breach>>

RecoveredWithinBudget ==
    /\ rollback = TRUE
    /\ dec_p95' \in Nat
    /\ dec_p95' <= 800
    /\ recovered' = TRUE
    /\ UNCHANGED <<breach, rollback>>

Stutter ==
    /\ UNCHANGED vars

Next ==
    \/ MeasureBreached
    \/ RollbackIssued
    \/ RecoveredWithinBudget
    \/ Stutter

Spec == Init /\ [][Next]_vars

Safety == [](breach => dec_p95 <= 1600)

Liveness ==
    WF_vars(RollbackIssued) /\
    WF_vars(RecoveredWithinBudget)

THEOREM Spec => Safety
====
