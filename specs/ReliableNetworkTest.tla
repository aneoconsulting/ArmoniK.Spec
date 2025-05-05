-------------------------- MODULE ReliableNetworkTest --------------------------
EXTENDS ReliableNetwork, TLC

(*****************************************************************************)
(* RELIABLE NETWORK TEST MODULE                                              *)
(*---------------------------------------------------------------------------*)
(* This module defines a simple test harness for the ReliableNetwork         *)
(* module using the TLC model checker. It tests operators and invariants.    *)
(*                                                                           *)
(* This module is designed for use with the TLC model checker.               *)
(*****************************************************************************)

--------------------------------------------------------------------------------
(*- CONSTANTS -*)

CONSTANT MaxSteps

--------------------------------------------------------------------------------
(*- VARIABLES -*)

VARIABLE numSteps

--------------------------------------------------------------------------------
(*- SPECIFICATION -*)

TestInit ==
    /\ InitNetwork
    /\ numSteps = 0

TestNext ==
    \/
        /\ numSteps < MaxSteps
        /\ numSteps' = numSteps + 1
        /\ \E p, q \in Processes:
            \/ \E m \in Messages:
                \/ Send(p, q, m)
                \/ Deliver(p, q, m)
            \/ \E m1, m2 \in Messages: Reply(p, q, m1, m2)
    \/ UNCHANGED << networkVars, numSteps >>

TestSpec ==
    TestInit /\ [][TestNext]_<< networkVars, numSteps >>

================================================================================