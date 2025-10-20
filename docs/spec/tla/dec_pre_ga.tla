---- MODULE dec_pre_ga ----
EXTENDS Naturals, Sequences, TLC

(**************************************************************************)
(* Variáveis de estado — anotações Snowcat em bloco                       *)
(* Use sempre:  (* @type: T; *) imediatamente acima da variável            *)
(**************************************************************************)
VARIABLES
(* @type: Int; *)
dec_p95,

(* @type: Bool; *)
breach,

(* @type: Bool; *)
rollback,

(* @type: Bool; *)
recovered

(* Tupla de variáveis para subscript de ações *)
vars == <<dec_p95, breach, rollback, recovered>>

(**************************************************************************)
(* Tipos esperados (reforço ao checker)                                    *)
(**************************************************************************)
TypeOK ==
/\ dec_p95 \in Nat
/\ breach \in BOOLEAN
/\ rollback \in BOOLEAN
/\ recovered \in BOOLEAN

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
(* Medida viola a meta de DEC (p95 > 800ms, com degradação controlada) *)
MeasureBreached ==
/\ dec_p95' \in Nat
/\ dec_p95' > 800
/\ dec_p95' <= 1600
/\ breach' = TRUE
/\ UNCHANGED <<rollback, recovered>>

(* Emite rollback quando há violação *)
RollbackIssued ==
/\ breach = TRUE
/\ rollback' = TRUE
/\ UNCHANGED <<dec_p95, recovered>>

(* Sistema recupera dentro do orçamento (p95 <= 800ms) *)
RecoveredWithinBudget ==
/\ rollback = TRUE
/\ dec_p95' \in Nat
/\ dec_p95' <= 800
/\ recovered' = TRUE
/\ UNCHANGED <<breach>>

(* Passo de stutter *)
Stutter ==
/\ dec_p95' = dec_p95
/\ breach' = breach
/\ rollback' = rollback
/\ recovered' = recovered

(* Dinâmica *)
Next == MeasureBreached / RollbackIssued / RecoveredWithinBudget / Stutter

(**************************************************************************)
(* Especificação, propriedades e teoremas                                  *)
(**************************************************************************)
Spec == Init /\ [][Next]_vars

(* Segurança: se há breach, p95 fica limitado por 1600ms (degradação controlada) *)
Safety == [](breach => dec_p95 <= 1600)

(* Vivacidade: sob justiça fraca das ações de rollback e recuperação *)
Liveness == WF_vars(RollbackIssued) /\ WF_vars(RecoveredWithinBudget)

THEOREM Spec => Safety
THEOREM Spec => []TypeOK
THEOREM Spec => <> <<RecoveredWithinBudget>>_vars

====
