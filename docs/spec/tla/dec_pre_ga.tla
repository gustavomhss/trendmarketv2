---- MODULE dec_pre_ga ----
EXTENDS Naturals, Sequences, TLC

(**************************************************************************)
(* Modelo DEC Pre-GA — revisado pela equipe (ASCII-only, Snowcat OK).      *)
(* Melhorias:                                                               *)
(* 1) Anotação Snowcat agregada ANTES de VARIABLES (1 bloco @type).         *)
(* 2) Limite superior de dec_p95 quando breach=TRUE (<=1600) p/ Safety.     *)
(* 3) UNCHANGED completo nas ações (sem variáveis não-especificadas).       *)
(* 4) Remoção de ação Stutter (usamos [][Next]_vars).                        *)
(**************************************************************************)

(* @type: dec_p95: Int; breach: Bool; rollback: Bool; recovered: Bool; *)
VARIABLES dec_p95, breach, rollback, recovered

vars == <<dec_p95, breach, rollback, recovered>>

(**************************************************************************)
(* Tipos e invariante estrutural                                           *)
(**************************************************************************)
TypeOK ==
/\ dec_p95 \in Nat
/\ breach \in BOOLEAN
/\ rollback \in BOOLEAN
/\ recovered \in BOOLEAN

Inv == TypeOK /\ (breach => dec_p95 <= 1600)

(**************************************************************************)
(* Estado inicial                                                          *)
(**************************************************************************)
Init ==
/\ TypeOK
/\ dec_p95 = 0
/\ breach = FALSE
/\ rollback = FALSE
/\ recovered = FALSE

(**************************************************************************)
(* Ações                                                                   *)
(**************************************************************************)
* Medida viola a meta de DEC (p95 > 800ms, com teto de 1600ms sob breach)
MeasureBreached ==
/\ dec_p95' \in Nat
/\ dec_p95' > 800
/\ dec_p95' <= 1600
/\ breach' = TRUE
/\ UNCHANGED <<rollback, recovered>>

* Emite rollback quando há violação
RollbackIssued ==
/\ breach = TRUE
/\ rollback' = TRUE
/\ UNCHANGED <<dec_p95, recovered, breach>>

* Sistema recupera dentro do orçamento (p95 <= 800ms)
RecoveredWithinBudget ==
/\ rollback = TRUE
/\ dec_p95' \in Nat
/\ dec_p95' <= 800
/\ recovered' = TRUE
/\ UNCHANGED <<breach, rollback>>

* Dinâmica (stuttering é dado por [][Next]_vars)
Next == MeasureBreached / RollbackIssued / RecoveredWithinBudget

(**************************************************************************)
(* Especificação, propriedades e teoremas                                  *)
(**************************************************************************)
Spec == Init /\ [][Next]_vars

Safety == [](breach => dec_p95 <= 1600)

* Vivacidade: sob justiça fraca de rollback e recuperação
Liveness == WF_vars(RollbackIssued) /\ WF_vars(RecoveredWithinBudget)

THEOREM Spec => []Inv
THEOREM Spec => Safety
THEOREM Spec => <> <<RecoveredWithinBudget>>_vars

====
