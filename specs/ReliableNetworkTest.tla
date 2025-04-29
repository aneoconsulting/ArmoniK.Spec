------------------------- MODULE ReliableNetworkTest -------------------------
EXTENDS ReliableNetwork, TLC

(*****************************************************************************)
(* RELIABLE NETWORK TEST MODULE                                              *)
(*---------------------------------------------------------------------------*)
(* This module defines a simple test harness for the ReliableNetwork         *)
(* module using the TLC model checker. It tests operators and invariants.    *)
(*                                                                           *)
(* This module is designed for use with the TLC model checker.               *)
(*****************************************************************************)

TestNext ==
    \E p, q \in ProcSet :
        \/ \E m \in Messages :
            \/ /\ Send(p, q, m)
               /\ Assert(m \in channel'[p][q], "Send failed!")
            \/ Deliver(p, q, m)
        \/ \E m1, m2 \in Messages : Reply(p, q, m1, m2)

TestSpec ==
    InitNetwork /\ [][TestNext]_networkVars

=============================================================================
