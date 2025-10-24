---- MODULE dec_pre_ga ----
EXTENDS Naturals, TLC

VARIABLES
\* @type: Int;
  dec_p95,
\* @type: Bool;
  breach,
\* @type: Bool;
  rollback,
\* @type: Bool;
  recovered

Init == TRUE

Next == UNCHANGED <<dec_p95, breach, rollback, recovered>>

Spec == Init /\ [][Next]_<<dec_p95, breach, rollback, recovered>>

====
