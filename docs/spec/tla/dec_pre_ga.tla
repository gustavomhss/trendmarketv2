---- MODULE dec_pre_ga ----
EXTENDS Naturals, Sequences, TLC

VARIABLES
    \* @type: Int;
    \* DEC p95 em milissegundos
    dec_p95,
    \* @type: Bool;
    \* flag de violação da meta DEC
    breach,
    \* @type: Bool;
    \* flag de rollback emitido
    rollback,
    \* @type: Bool;
    \* sistema recuperado dentro do orçamento
    recovered
\* Corrigido: anotações Snowcat para variáveis de estado

vars == <<dec_p95, breach, rollback, recovered>>

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

Spec == Init /\ [][Next]_vars

Safety == [](breach => dec_p95 <= 1600)

Liveness == WF_vars(RollbackIssued) /\
            WF_vars(RecoveredWithinBudget)

THEOREM Spec => Safety
\* Corrigido: ação sob <> deve estar na forma <<A>>_vars (SANY)
THEOREM Spec => <> <<RecoveredWithinBudget>>_vars

====
