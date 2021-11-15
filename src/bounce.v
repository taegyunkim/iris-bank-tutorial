(*! A simple demo of Iris and Coq following tchajed/iris-bank-demo and article
https://plv.csail.mit.edu/blog/iris-intro.html *)

From iris.base_logic Require Import lib.ghost_var.

(* This code is written in HeapLang, a simple ML-like language shipped with
Iris. *)
From iris.heap_lang Require Import proofmode notation adequacy assert.
From iris.heap_lang.lib Require Import lock spin_lock.

Require Import Bool.

(* set some Coq options for basic sanity *)
(* https://coq.inria.fr/distrib/V8.13.0/refman/proofs/writing-proofs/proof-mode.html#proof-using-options
*)
Set Default Proof Using "All".
(* Using Default Goal Selector with the ! selector forces tactic scripts to keep
focus to exactly one goal (e.g. using bullets) or use explicit goal selectors.*)
Set Default Goal Selector "!".
Set Printing Projections.
(* interpret arithmetic operations over Z, integer scope.
There is also something like nat_scope, probably both from Coq. *)
Open Scope Z_scope.


Section bounce_code.

  Definition new_bounce_unit : val :=
    λ: "id",
    let: "id_ref" := ref "id" in
    let: "phase_ref" := ref #1 in
    ("id_ref", "phase_ref").

  Definition get_id : val :=
    λ: "bounce_unit",
    let: "id" := !(Fst "bounce_unit") in
    "id".

  Definition set_id: val :=
    λ: "bounce_unit" "new_id",
    let: "id_ref" := Fst "bounce_unit" in
    "id_ref" <- "new_id";;
    #().

  Definition get_phase: val :=
    λ: "bounce_unit",
    let: "phase" := !(Snd "bounce_unit") in
    "phase".

  Definition phase_transit: val :=
    λ: "bounce_unit",
    let: "phase_ref" := !(Snd "bounce_unit") in
    match !"phase_ref" with
    | #1 => "phase_ref" <- #2
    | #2 => "phase_ref" <- #3
    | #3 => "phase_ref" <- #1
    | _ => assert: #false (* don't handle all other cases. *)
    end.

End bounce_code.

Section bounce_spec.
Context `{!heapGS Σ, lockG Σ}.

Local Notation iProp := (iProp Σ).

Definition is_bounce_unit (b: val) (id: val) : iProp :=
  (∃ (id_ref phase_ref: loc) p, ⌜b = (#id_ref, #phase_ref)%V⌝ ∗ id_ref ↦ id ∗
    phase_ref ↦ p)%I.

Theorem wp_new_bounce_unit (id: val):
  {{{ True }}}
  new_bounce_unit id
  {{{b, RET b; is_bounce_unit b id}}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec.
  wp_alloc id_ref as "Hid".
  wp_alloc phase_ref as "Hphase".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iExists _, _, _; by iFrame.
Qed.

Theorem wp_get_id (b: val) (id: val):
  {{{ is_bounce_unit b id }}}
    get_id b
  {{{id, RET id; True }}}.
Proof.
  iIntros (Φ) "Hb HΦ".
  iDestruct "Hb" as (id_ref phase_ref p) "[% [Hi Hp]]"; subst.
  wp_rec.
  wp_pures.
  wp_load.
  wp_pures.
  iModIntro.
  iApply "HΦ".
  auto.
Qed.

Theorem wp_set_id (b: val) (id: val) (id': val):
  {{{ is_bounce_unit b id }}}
    set_id b id'
  {{{RET #(); is_bounce_unit b id'}}}.
  iIntros (Φ) "Hb HΦ".
  iDestruct "Hb" as (id_ref phase_ref p) "[% [Hi Hp]]"; subst.
  wp_rec.
  wp_pures.
  wp_store.
  iApply "HΦ".
  iModIntro.
  iExists _, _, _; by iFrame.
Qed.

Theorem wp_get_phase (b: val) (id: val):
  {{{ is_bounce_unit b id  }}}
    get_phase b
  {{{p, RET p; True}}}.
Proof.
  iIntros (Φ) "Hb HΦ".
  iDestruct "Hb" as (id_ref phase_ref p) "[% [Hi Hp]]"; subst.
  wp_rec.
  wp_pures.
  wp_load.
  wp_let.
  iModIntro.
  iApply "HΦ".
  iPureIntro.
  reflexivity.
Qed.


(*
Theorem wp_new_bounce_unit (id: val):
  {{{ True }}}
    new_bounce_unit id
  {{{b, RET b; is_bounce_unit b id}}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec.
  wp_alloc id_ref as "Hid".
  wp_alloc phase_ref as "Hphase".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iExists _, _, _.
  iSplit.
  - by iFrame.
  - iFrame.
Qed.

Theorem wp_get_id (b: val) (id: val):
  {{{ is_bounce_unit b id }}}
    get_id b
  {{{id, RET id; True}}}.
Proof.
  iIntros (Φ) "Hb HΦ".
  wp_pures.
  iDestruct "Hb" as (id_ref phase_ref phase) "[% [Hi Hp]]"; subst.
  wp_rec.
  wp_pures.
  wp_load.
  wp_let.
  iModIntro.
  iApply "HΦ".
  auto.
Qed.

Theorem wp_set_id (b: val) (id: val) (id': val):
  {{{ is_bounce_unit b id }}}
    set_id b id'
  {{{RET #(); is_bounce_unit b id'}}}.
Proof.
  iIntros (Φ) "Hb HΦ".
  iDestruct "Hb" as (id_ref p_ref phase)  "[% [Hi Hp]]"; subst.
  wp_lam.
  wp_pures.
  wp_store.
  unfold is_bounce_unit.
  iDestruct "HΦ" as (id_ref' p_ref' phase') "[Hb [Hi Hp]]".
  iApply "HΦ".







Lemma get_id_spec (b: val):
  {{{ is_bounce_unit b }}}
    get_id b
  {{{ id, RET id; ⌜(id = #0)%V⌝ }}}.
Proof.
  iIntros (Φ) "Hb HΦ".
  iDestruct "Hb" as
  iDestruct
  wp_rec.
  wp_pures.

  wp_load.
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iPureIntro.
  reflexivity.
Qed.

Lemma set_id_spec (b: val) (i: val) :
  {{{ is_bounce_unit b}}}
    set_id b i;;
    get_id b
  {{{ id, RET id; ⌜(id = i)%V⌝}}}.
Proof.
  iIntros (Φ) "Hb HΦ".
  iDestruct "Hb" as (id_ref p_ref) "[% [Hi Hp]]"; subst.
  wp_lam.
  wp_pures.
  wp_store.
  wp_pures.
  wp_lam.
  wp_pures.
  wp_load.
  wp_let.
  iModIntro.
  iApply "HΦ".
  iPureIntro.
  reflexivity.
Qed.

Lemma get_phase_sepc (b: val) (i: val) (p: val):
  {{{ is_bounce_unit b i p }}}
    get_phase b
  {{{ phase, RET phase; ⌜(phase = p)%V⌝ }}}.
Proof.
  iIntros (Φ) "Hb HΦ".
  unfold is_bounce_unit.
  iDestruct "Hb" as (id_ref phase_ref) "[% [Hi Hp]]"; subst.
  wp_rec.
  wp_pures.
  wp_load.
  wp_let.
  iModIntro.
  iApply "HΦ".
  iPureIntro.
  reflexivity.
Qed.

Definition phase_transit_demo: val :=
  λ: <>,
  let: "b" := new_bounce_unit #() in
  Fork(phase_transit "b");;
  let: "ok" := (get_phase "b") = #2 in
  "ok".

Theorem wp_phase_transit_demo:
  {{{ True }}}
  phase_transit_demo #()
  {{{ RET #true; True}}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec.
  wp_apply new_bounce_unit_spec; first auto.
  iIntros (b) "#Hb". wp_pures.
  wp_apply wp_fork.
  - wp_rec.
  wp_pure.
  wp_let.
  wp_rec.

Lemma phase_inv (b: val) (i: val) (p: val):
  {{{ is_bounce_unit b i p ∗  }}}
    phase_transit b;; get_phase b
  {{{ p', RET p'; ⌜p' = #1 ∨ p' = #2 ∨ p' = #3⌝%V  }}}.
Proof.
  iIntros (Φ) "Hb HΦ".
  iDestruct "Hb" as (id_ref phase_ref) "[% [Hi Hpref]]"; subst.
  wp_rec.
  iCombine "Hp Hpref" as "Hp'".
  iRewrite

  wp_rec.
  wp_pures.
  wp_load.

End bounce_spec. *)


(* Definition new_bounce_unit: val :=
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

Definition bounce_unit_inv (b: val) id :iProp Σ :=
  ∃ (id_ref phase_ref signed_ref num_precommits_ref num_noncommits_ref: loc),
      ⌜b = (
        #id_ref, #phase_ref, #signed_ref,
        #num_precommits_ref, #num_noncommits_ref)%V⌝ ∗ id_ref ↦ id.

Lemma check_new_bounce_unit:
    {{{ True }}}
        new_bounce_unit #1
    {{{b, RET b; bounce_unit_inv b #1 }}}.
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
  iExists _, _, _, _, _.
  iSplit.
  { by iFrame.  }
  by iFrame.
Qed.

Definition get_id_inv (b:val) : iProp Σ :=
  ∃ (id_ref: loc), ⌜get_id b = #id_ref%V⌝ ∗ ∃ (id: Z), id_ref ↦ #id.

Theorem wp_get_id:
  {{{ True }}}
    new_bounce_unit #1
  {{{b, RET b; get_id_inv b}}}.
Proof.
  iIntros (Φ) "_ HΦ".
  unfold bounce_unit_inv.
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
  unfold get_id_inv.
  iExists id_ref.
  iSplit.
  {
    iPureIntro.
  }


  iPureIntro.
  unfold get_id.
  simpl.


End check. *)

(*
Definition new_bounce_unit: val :=
    λ: <>,
    let: "phase" := ref #1 in
    let: "some_other" := ref #2 in
    ("phase", "some_other"). *)

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

(* Definition phase_transition: val :=
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
    | Noncommit *)


(* This function returns a list or array of bounce units, which we call a
flock *)
(* Definition new_flock: val:=
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
End proof. *)

(* When do you need to use Iris over Coq?
For this just Coq would not be enough.
*)


(* Definition phase_transit : val :=
    λ: <>,
    let: "bounce_unit" := new_bounce_unit #() in
    Fork (phase_transition "bounce_unit");;
    Zeq_bool !Fst ("bounce_unit") #2. *)