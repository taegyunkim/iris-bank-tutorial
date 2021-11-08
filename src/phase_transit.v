(* In this file we explain how to do the "parallel increment" example (Example
   7.5) from the lecture notes in Iris in Coq. *)

(* Contains definitions of the weakest precondition assertion, and its basic
   rules. *)
From iris.program_logic Require Export weakestpre.
(* Definition of invariants and their rules (expressed using the fancy update
    modality). *)
From iris.base_logic.lib Require Export invariants.

(* Files related to the interactive proof mode. The first import includes the
    general tactics of the proof mode. The second provides some more specialized
    tactics particular to the instantiation of Iris to a particular programming
    language. *)
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.

(* Instantiation of Iris with the particular language. The notation file
    contains many shorthand notations for the programming language constructs, and
    the lang file contains the actual language syntax. *)
From iris.heap_lang Require Import notation adequacy.

(* We also import the parallel composition construct. This is not a primitive of
    the language, but is instead derived. This file contains its definition, and
    the proof rule associated with it. *)
From iris.heap_lang.lib Require Import par.

(* The following line imports some Coq configuration we commonly use in Iris
    projects, mostly with the goal of catching common mistakes. *)
From iris.prelude Require Import options.

(* We define our terms. The Iris Coq library defines many notations for
    programming language constructs, e.g., lambdas, allocation, accessing and so
    on. The complete list of notations can be found in
    theories/heap_lang/notations.v file in the iris-coq repository.
    The # in the notation is used to embed literals, e.g., variables, numbers, as
    values of the programmin language. *)

(*
Inductive Phase :=
    | First
    | Second
    | Third.

Definition phase_incr (p : Phase) : Phase :=
    match p with
    | First => Second
    | Second => Third
    | Third => First
    end.

Definition phase_transit (p: loc) :=
    match !#p with
        | #First => p <- Second
        | #Second => p <- Third
        | #Third => p <- First
    end.



Definition phase_eq (p: Phase) (q: Phase) : Prop := *)
    (* q = p. *)
    (* match p with
    | First => match q with
                | First => true
                | _ => false
                end
    | Second => match q with
                 | Second => true
                 | _ => false
                 end
    | First First => True
    | Second Second => True
    | Third Third => True
    | _ _ => False
    end. *)


(*
(* We define the heap as a list of pairs (variable, value). *)

Definition phase_transit (p: loc) : expr :=
    match !#p with
        S => #p <- SS
      | SS => #p <- SSS
      | #_ => #p <- S
    end.
 *)

(* Inductive Phase :=
    | First
    | Second
    | Third. *)

Definition phase_transit: expr :=
    λ: "l",
    let: "phase" := !"l" in
    match !"phase" with
        #1 => "l" <- #2
      | #2 => "l" <- #3
      | _ => "l" <- #1
      (* | #3 => "l" <- #1
      (* Throw an error in this case,
        or probably try with Inductive. *)
      | _ => #-1 *)
    end.

(*
process_msg :=
    λ: "bounce" "msg",
*)

Section proof.
(* In order to do the proof we need to assume certain things about the
    instantiation of Iris. The particular, even the heap is handled in an
    analogous way as other ghost state. This line states that we assume the
    Iris instantiation has sufficient structure to manipulate the heap, e.g.,
    it allows us to use the points-to predicate. *)
Context `{!heapGS Σ}.
(* Recall that parallel composition construct is defined in terms of fork. To
    prove the expected rules for this construct we need some particular ghost
    state in the instantiation of Iris, as explained in the lecture notes. The
    following line states that we have this ghost state. *)
Context `{!spawnG Σ}.
(* The variable Σ has to do with what ghost state is available, and the type
    of Iris propositions (written Prop in the lecture notes) depends on this Σ.
    But since Σ is the same throughout the development we shall define
    shorthand notation which hides it. *)
Notation iProp := (iProp Σ).
(* As in the paper proof we will need an invariant to share access to a
    location. This invariant will be allocated in this namespace which is a
    parameter of the whole development. *)
Context (N : namespace).
(*
Definition phase_incr_inv (p: Phase) :iProp :=
    (∃ (q: Phase), ⌜(phase_incr p) = q⌝)%I.

Lemma phase_incr_spec (p: Phase) :
    {{{ True }}} phase_incr First {{{ RET Second; True}}}. *)

(*
Lemma check_phase_transit_3 (p: loc) :
    {{{ p ↦ #3 }}}
        phase_transit p
    {{{ RET #1 ; True }}}.
Proof using Type* N.
    iIntros (Φ) "Hpt HΦ".
    iMod (inv_alloc N _ _ with "Hpt") as "HInv".

    destruct phase_transit. *)
(*
Definition wp: expr :=
    λ: "1", let: "n" := !"1" in "1" <- "n" + #2.

Lemma wp_example (l:loc):
    {{{l ↦ #1 }}}
        wp #l
    {{{ RET #() ;  l ↦ #3}}}.
Proof.
    iIntros (Φ) "Hpt HΦ".
    wp_pures.
    wp_load.
    wp_store.
    iModIntro.
    iApply "HΦ".
    iFrame.
Qed. *)

Lemma phase_transit_3 (l:loc):
{{{l ↦ #3 }}}
    phase_transit #l
{{{ RET #() ;  l ↦ #1}}}.
Proof.
    iIntros (Φ) "Hpt HΦ".
    unfold phase_transit.
    wp_pures.
    wp_load.

    wp_store.
    iModIntro.
    iApply "HΦ".
    iFrame.
Qed.

End proof.
