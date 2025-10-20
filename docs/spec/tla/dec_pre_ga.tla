---- MODULE dec_pre_ga ----
EXTENDS Naturals, TLC

(***************************************************************************)
(* Modelo mínimo para Gate Pre-GA (DEC).                                   *)
(* Regras: ASCII puro; sem Unicode; Next bem-formado; Snowcat 1 bloco.     *)
(***************************************************************************)

(*
  @type: dec_p95: Int;
         breach: Bool;
         rollback: Bool;
         recovered: Bool;
*)
VARIABLES dec_p95, breach, rollback, recovered

vars == <<dec_p95, breach, rollback, recovered>>

(***************************************************************************)
(* Tipagem e estado inicial                                                *)
(***************************************************************************)
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

(***************************************************************************)
(* Ações                                                                    *)
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

Next ==
  \/ MeasureBreached
  \/ RollbackIssued
  \/ RecoveredWithinBudget
  \/ Stutter

(***************************************************************************)
(* Especificação e propriedade checada no ORR                              *)
(***************************************************************************)
Spec == Init /\ [][][Next]_vars  \* Nota: [][][A]_v == []([A]_v)

Safety == [](breach => dec_p95 <= 1600)

THEOREM Spec => Safety

====
