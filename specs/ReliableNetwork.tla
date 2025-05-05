---------------------------- MODULE ReliableNetwork ----------------------------
EXTENDS Bags, Naturals, Utils

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
(*****************************************************************************)

--------------------------------------------------------------------------------
(*- CONSTANTS -*)

CONSTANTS
    Processes,  \* The set of process identifiers.
    Messages    \* The set of messages the network can carry.

--------------------------------------------------------------------------------
(*- VARIABLES -*)

VARIABLES
    channel     \* channel[s][r] is the unordered set of messages in the
                \* channel from sender s to receiver r.

networkVars == << channel >>

--------------------------------------------------------------------------------
(*- INVARIANTS -*)

NetworkTypeInvariant ==
    \A i \in Processes:
        \A j \in Processes \ {i}:
            \E Msgs \in SUBSET Messages:
                channel[i][j] \in [Msgs -> Nat]

--------------------------------------------------------------------------------
(*- ACTIONS -*)

InitNetwork ==
    (*************************************************************************)
    (* Initializes network with all channels empty.                          *)
    (*************************************************************************)
    channel = [p \in Processes |-> [q \in Processes \ {p} |-> EmptyBag]]

Send(s, r, m) ==
    (*************************************************************************)
    (* Adds a message m to the unordered buffer channel[s][r]. Used when a   *)
    (* process s sends a message to process r.                               *)
    (*************************************************************************)
    /\ s \in Processes
    /\ r \in Processes
    /\ s /= r
    /\ channel' = [channel EXCEPT ![s][r] = BagAdd(@, m)]

Deliver(r, s, m) ==
    (*************************************************************************)
    (* Removes a message m from the buffer channel[s][r]. Used when a        *)
    (* process r is done processing a message sent by s.                     *)
    (*************************************************************************)
    /\ r \in Processes
    /\ s \in Processes
    /\ s /= r
    /\ m \in DOMAIN channel[s][r]
    /\ channel' = [channel EXCEPT ![s][r] = BagRemove(@, m)]

Reply(s, r, m1, m2) ==
    (*************************************************************************)
    (* Combination of Send and Deliver. Used when a process r processed a    *)
    (* message m1 from s and immediately respond to it with message m2.      *)
    (*************************************************************************)
    /\ Deliver(s, r, m1)
    /\ Send(r, s, m2)

================================================================================