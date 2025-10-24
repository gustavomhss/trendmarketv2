---- MODULE dec_pre_ga ----
EXTENDS Integers, Naturals, TLC
\* Integers provides the Int set required by the Apalache checker.

VARIABLES
\* @type: Int;
  dec_p95,
\* @type: Bool;
  breach,
\* @type: Bool;
  rollback,
\* @type: Bool;
  recovered

Threshold == 800

Init ==
  /\ dec_p95 = 0
  /\ dec_p95 \in Nat
  /\ breach = FALSE
  /\ rollback = FALSE
  /\ recovered = FALSE

Next ==
  \E new_p95 \in Nat:
    /\ dec_p95' = new_p95
    /\ breach' = (new_p95 > Threshold)
    /\ rollback' = IF breach' THEN TRUE ELSE rollback
    /\ recovered' = IF rollback /\ (new_p95 <= Threshold) THEN TRUE ELSE recovered

Spec == Init /\ [][Next]_<<dec_p95, breach, rollback, recovered>>

====
