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

Init ==
  /\ dec_p95 \in Int
  /\ breach \in BOOLEAN
  /\ rollback \in BOOLEAN
  /\ recovered \in BOOLEAN

Next ==
  /\ dec_p95' = dec_p95
  /\ breach' = breach
  /\ rollback' = rollback
  /\ recovered' = recovered

Spec == Init /\ [][Next]_<<dec_p95, breach, rollback, recovered>>

====
