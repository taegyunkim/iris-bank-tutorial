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
  λ: "id",
  let: "id_ref" := ref "id" in
  let: "phase" := ref #1 in
  let: "signed" := ref #2 in
  let: "num_precommits" := ref #3 in
  let: "num_noncommits" := ref #4 in
  ("id_ref", "phase", "signed", "num_precommits", "num_noncommits").

Definition get_id: val :=
    λ: "bounce_unit",
    !(Fst "bounce_unit").

Definition get_phase: val :=
    λ: "bounce_unit",
    !(Fst(Snd "bounce_unit")).

Definition get_signed: val :=
    λ: "bounce_unit",
    !(Fst(Snd(Snd "bounce_unit"))).

Definition get_num_precommits: val :=
    λ: "bounce_unit",
    !(Fst(Snd(Snd(Snd "bounce_unit")))).

Definition get_num_noncommits: val :=
    λ: "bounce_unit",
    !(Snd(Snd(Snd(Snd "bounce_unit")))).

Section check.
(* mostly standard boilerplate *)
Context `{!heapGS Σ}.
Context `{!lockG Σ}.
(* Z refers to the type of integers *)
Context `{!ghost_varG Σ Z}.
Let N := nroot.@"check".

Definition bounce_unit_inv (b: val) :iProp Σ :=
  ∃ (id_ref phase_ref signed_ref num_precommits_ref num_noncommits_ref: loc),
      ⌜b = (
        #id_ref, #phase_ref, #signed_ref,
        #num_precommits_ref, #num_noncommits_ref)%V⌝.

Lemma check_new_bounce_unit:
    {{{ True }}}
        new_bounce_unit #1
    {{{b, RET b; bounce_unit_inv b }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec.
  wp_alloc id_ref as "Hid".
  wp_alloc phase_ref as "Hphase".
  wp_alloc signed_ref as "Hsigned".
  wp_alloc num_precommits_ref as "Hnum_precommits".
  wp_alloc num_noncommits_ref as "Hnum_noncommits".
  wp_let.
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iExists _, _, _, _, _; by iFrame.
Qed.
End check.


Definition new_bounce_unit: val :=
    λ: <>,
    let: "phase" := ref #1 in
    let: "some_other" := ref #2 in
    ("phase", "some_other").

(*
    ("phase", ("second", "third"))

    struct like datatype in coq/iris?

    Define constructor taking n number of arguments
    and define accessors for each of those arguments

    Definition new_bounce_unit: val :=
    λ: "f1" "f2" "f3" ... "fn"
    ("f1", "f2", "f3", ..., "fn")
    ...
    but still you have to access "f2" as Fst Snd "bounce_unit"
    "f3" as Fst Snd Snd "bounce_unit"

    Definition get_f1: val :=
    λ: "bounce_unit",
        Fst "bounce_unit"

*)

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

Definition phase_transition_two : val :=
    λ: "bounce",
    let: "phase" := "bounce" in
    match !"phase" with
      #3 => Fst "bounce" <- #1
      | _ => Fst "bounce" <- !"phase" + #1
    end.

Definition check_phase: val :=
    λ: "bounce_unit" "phase",
    let: "bounce_phase" := Fst "bounce" in
    let: "ok":= !"bounce_phase" = "phase" in
    "ok".

(* Define messages *)
Inductive message: Type :=
    | Precommit
    | Noncommit


(* This function returns a list or array of bounce units, which we call a
flock *)
Definition new_flock: val:=
    λ: <>,
    #1.

(* The shared last broadcast bus.*)
Definition new_bus: val:=
    λ: <>,
    #2.

(* This corresponds to what bounce unit i does to update its state*)
Definition read_bus_update_state: val :=
    λ: "bus" "flock" "i",
    #3.

Definition update_bus: val :=
    λ: "bus" "i",
    #4.

Section proof.

Context `{!heapGS Σ}.
Context `{!spawnG Σ}.
Context `{!ghost_varG Σ Z}.
Notation iProp := (iProp Σ).
Context (N : namespace).


Definition phase_inv γ phase_ref : iProp :=
    ∃ (phase: Z), phase_ref ↦ #phase ∗ ghost_var γ (1/2) phase ∗
    ⌜(phase = 1)%Z ∨ (phase = 2)%Z ∨ (phase = 3)%Z⌝.


Definition is_bounce_unit (b: val) : iProp :=
    ∃ (phase_ref: loc) (γ: gname),
        ⌜b = (#phase_ref, #2)%V⌝ ∗ phase_inv γ phase_ref.

Theorem wp_new_bounce_unit:
    {{{True}}}
        new_bounce_unit #()
    {{{b, RET b; is_bounce_unit b}}}.
Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (* TODO *)
Admitted.
End proof.

(* When do you need to use Iris over Coq?
For this just Coq would not be enough.
*)


(* Definition phase_transit : val :=
    λ: <>,
    let: "bounce_unit" := new_bounce_unit #() in
    Fork (phase_transition "bounce_unit");;
    Zeq_bool !Fst ("bounce_unit") #2. *)