(*! A simple demo of Iris and Coq following tchajed/iris-bank-demo and article
https://plv.csail.mit.edu/blog/iris-intro.html *)

From iris.base_logic Require Import lib.ghost_var.

(* This code is written in HeapLang, a simple ML-like language shipped with
Iris. *)
From iris.heap_lang Require Import proofmode notation adequacy.
From iris.heap_lang.lib Require Import lock spin_lock.

Require Import Bool.

(* set some Coq options for basic sanity *)
(* https://coq.inria.fr/distrib/V8.13.0/refman/proofs/writing-proofs/proof-mode.html#proof-using-options
*)
Set Default Proof Using "Type".
(* Using Default Goal Selector with the ! selector forces tactic scripts to keep
focus to exactly one goal (e.g. using bullets) or use explicit goal selectors.*)
Set Default Goal Selector "!".
Set Printing Projections.
(* interpret arithmetic operations over Z, integer scope.
There is also something like nat_scope, probably both from Coq. *)
Open Scope Z_scope.

Definition new_bounce_unit: val :=
    λ: <>,
    let: "phase" := ref #1 in
    let: "some_other" := ref #2 in
    ("phase", "some_other").

(*
Definition phase_transition : val :=
    λ: "bounce_unit",
    let: "phase" := !(Fst "bounce_unit") in
    if Zeq_bool "phase" 3 then (Fst "bounce_unit") <- #1 else Fst("bounce_unit") <- "phase" + #1
    #(). *)

Definition phase_transition: val :=
    λ: "bounce",
    let: "phase" := Fst "bounce" in
    match !"phase" with
        #1 => Fst "bounce" <- #2
      | #2 => Fst "bounce" <- #3
      | _ => Fst "bounce" <- #1
    end.

Definition check_phase: val :=
    λ: "bounce_unit" "phase",
    let: "bounce_phase" := Fst "bounce" in
    let: "ok":= !"bounce_phase" = "phase" in
    "ok".

Definition phase_transit: expr :=
    λ: <>,
    let: "bounce_unit" := new_bounce_unit #() in
    phase_transition "bounce_unit";;
    check_phase "bounce_unit" #2.


(* Definition phase_transit : val :=
    λ: <>,
    let: "bounce_unit" := new_bounce_unit #() in
    Fork (phase_transition "bounce_unit");;
    Zeq_bool !Fst ("bounce_unit") #2. *)