---- MODULE dec_pre_ga ----
EXTENDS Naturals, Sequences, TLC

\* @type: dec_p95: Int; breach: Bool; rollback: Bool; recovered: Bool;

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

\* Medida viola a meta de DEC (p95 > 800ms; teto 1600ms sob degradacao)
MeasureBreached ==
    /\ dec_p95' \in Nat
    /\ dec_p95' > 800
    /\ dec_p95' <= 1600
    /\ breach' = TRUE
    /\ UNCHANGED <<rollback, recovered>>

\* Emite rollback quando ha violacao
RollbackIssued ==
    /\ breach = TRUE
    /\ rollback' = TRUE
    /\ UNCHANGED <<dec_p95, recovered, breach>>

\* Sistema recupera dentro do orcamento (p95 <= 800ms)
RecoveredWithinBudget ==
    /\ rollback = TRUE
    /\ dec_p95' \in Nat
    /\ dec_p95' <= 800
    /\ recovered' = TRUE
    /\ UNCHANGED <<breach, rollback>>

\* Dinamica (stuttering implicito via [][])
Next == MeasureBreached \/ RollbackIssued \/ RecoveredWithinBudget

Spec == Init /\ [][Next]_vars

\* Seguranca: se ha breach, p95 fica limitado por 1600ms (degradacao controlada)
Safety == [](breach => dec_p95 <= 1600)

\* Vivacidade sob justica fraca
Liveness == WF_vars(RollbackIssued) /\ WF_vars(RecoveredWithinBudget)

THEOREM Spec => Safety
THEOREM Spec => <> <<RecoveredWithinBudget>>_vars

====
