Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
Import ListNotations.
From WS  Require Import Basics.
From WS  Require Import Tactics.
From WS  Require Import States.
From WS  Require Import Lists.
From WS  Require Import Multi.
From WS  Require Import Imp.

(* 
  The notion of a 'program context' is introduced
    by Brookes in section 4 (Program Behavior), and
    notated by his as P[-]. It is defined as a
    program with a hole, into which a command may be 
    substituted.
  This file translates this notion into Coq.
*)

(* 
  Definition of a program context.
  Note that since a program context must contain 
    one and only one hole, a context is either a hole,
    or mimics some complex program structure, where one
    of the inner commands contains a hole.
*)
Inductive context : Type :=
  | CXTSeq1  : context -> com     -> context
  | CXTSeq2  : com     -> context -> context
  | CXTIf1   : bexp    -> context -> com     -> context
  | CXTIf2   : bexp    -> com     -> context -> context
  | CXTWhile : bexp    -> context -> context
  | CXTPar1  : context -> com     -> context
  | CXTPar2  : com     -> context -> context
  | CXTAwait : bexp    -> context -> context
  | CXTHole  : context.

(* 
  This function represents substituting a command
    into a program context.
  I.e. plug P c = P[-] |-> c |-> P[c] using Brookes's 
    notations.
*)
Fixpoint plug (cxt : context) (p : com) : com :=
  match cxt with
  | CXTSeq1 cxt c  => CSeq (plug cxt p) c
  | CXTSeq2 c cxt  => CSeq c (plug cxt p) 
  | CXTIf1 b cxt c => CIf b (plug cxt p) c
  | CXTIf2 b c cxt => CIf b c (plug cxt p) 
  | CXTWhile b cxt => CWhile b (plug cxt p) 
  | CXTPar1 cxt c  => CPar (plug cxt p) c
  | CXTPar2 c cxt  => CPar c (plug cxt p) 
  | CXTAwait b cxt => CAwait b (plug cxt p) 
  | CXTHole        => p
  end.