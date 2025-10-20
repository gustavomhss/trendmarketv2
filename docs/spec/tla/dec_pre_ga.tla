---- MODULE dec_pre_ga ----
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(* State variables with Snowcat type hints (one @type per identifier).      *)
(***************************************************************************)
VARIABLES
(* @type: Int;  *) dec_p95,   * DEC p95 in milliseconds
(* @type: Bool; *) breach,    * threshold breach flag
(* @type: Bool; *) rollback,  * rollback issued
(* @type: Bool; *) recovered  * system recovered within budget

vars == <<dec_p95, breach, rollback, recovered>>

(***************************************************************************)
(* Type expectations                                                       *)
(***************************************************************************)
TypeOK ==
/\ dec_p95 \in Nat
/\ breach \in BOOLEAN
/\ rollback \in BOOLEAN
/\ recovered \in BOOLEAN

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
/\ TypeOK
/\ dec_p95 = 0
/\ breach = FALSE
/\ rollback = FALSE
/\ recovered = FALSE

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
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

Next == MeasureBreached / RollbackIssued / RecoveredWithinBudget / Stutter

(***************************************************************************)
(* Specification and properties                                            *)
(***************************************************************************)
Spec == Init /\ [] [Next]_vars

Safety == [] (breach => dec_p95 <= 1600)

Liveness == WF_vars(RollbackIssued) /\ WF_vars(RecoveredWithinBudget)

THEOREM Spec => Safety
THEOREM Spec => <> <<RecoveredWithinBudget>>_vars

====
