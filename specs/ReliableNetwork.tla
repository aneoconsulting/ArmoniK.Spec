--------------------------- MODULE ReliableNetwork ---------------------------
EXTENDS FiniteSets, Naturals

(*****************************************************************************)
(* RELIABLE NETWORK MODULE                                                   *)
(*---------------------------------------------------------------------------*)
(* Models a fully connected reliable network that interconnects a set of     *)
(* processes. It is agnostic to message semantics.                           *)
(*                                                                           *)
(* This module simulates an idealized TCP/IP network. The lack of message    *)
(* ordering within channels allows for the modeling of multi-threaded        *)
(* systems.                                                                  *)
(*                                                                           *)
(* Properties:                                                               *)
(* - Reliable Delivery:   Messages are never lost, duplicated, or corrupted. *)
(* - Unordered Delivery:  Messages may be delivered in any order (no FIFO).  *)
(* - Fully Connected:     Each process has a direct channel with every other *)
(*                        process.                                           *)
(* - Unbounded Buffers:   Channels can store any number of messages of any   *)
(*                        size.                                              *)
(* - No message creation: Messages are only added through sends.             *)
(*                                                                           *)
(* Operators:                                                                *)
(* - Send(s, r, m):       Adds a message m to the unordered buffer           *)
(*                        channel[s][r]. Used when a process s sends a       *)
(*                        message to process r.                              *)
(* - Deliver(r, s, m):    Removes a message m from the buffer channel[s][r]. *)
(*                        Used when a process r is done processing a message *)
(*                        sent by s.                                         *)    
(* - Reply(s, r, m1, m2): Combination of Send and Deliver. Used when a       *)
(*                        process r processed a message m1 from s and        *)
(*                        immediately respond to it with message m2.         *)
(*                                                                           *)
(* Invariants:                                                                *)
(* - NetworkTypeInvariant: Type invariance property for module internal      *)
(*   variables.                                                              *)
(*****************************************************************************)

-------------------------------------------------------------------------------
(*- CONSTANTS -*)
CONSTANTS
    ProcSet,    \* The set of process identifiers.
    Messages    \* The set of messages the network can carry.

-------------------------------------------------------------------------------
(*- VARIABLES -*)

VARIABLES
    channel     \* channel[s][r] is the unordered set of messages in the
                \* channel from sender s to receiver r.

networkVars == <<channel>>

-------------------------------------------------------------------------------
(*- INVARIANTS -*)

NetworkTypeInvariant ==
    /\ channel \in [ProcSet -> [ProcSet -> SUBSET Messages]]
    /\ \A i \in ProcSet : channel[i][i] = {}

-------------------------------------------------------------------------------
(*- OPERATORS -*)

(* Initializes network with all channels empty. *)
InitNetwork ==
    channel = [p \in ProcSet |-> [q \in ProcSet |-> {}]]

(* Adds a message m to the unordered buffer channel[s][r]. Used when a process
   s sends a message to process r. *)
Send(s, r, m) ==
    /\ s \in ProcSet
    /\ r \in ProcSet
    /\ s # r
    /\ channel' = [channel EXCEPT ![s][r] = @ \union {m}]

(* Removes a message m from the buffer channel[s][r]. Used when a process r is
   done processing a message sent by s. *)
Deliver(r, s, m) ==
    /\ r \in ProcSet
    /\ s \in ProcSet
    /\ s # r
    /\ m \in channel[s][r]
    /\ channel' = [channel EXCEPT ![s][r] = @ \ {m}]

(* Combination of Send and Deliver. Used when a process r processed a message
   m1 from s and immediately respond to it with message m2. *)
Reply(s, r, m1, m2) ==
    /\ Deliver(s, r, m1)
    /\ Send(r, s, m2)

===============================================================================
