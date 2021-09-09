From iris.base_logic Require Import lib.ghost_var.

From iris.heap_lang Require Import proofmode notation adequacy.
From iris.heap_lang.lib Require Import lock spin_lock.

(* set some Coq options for basic sanity *)
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Set Printing Projections.
Open Scope Z_scope.

Definition new_bank: val :=
    λ: <>,
    let: "a_bal" := ref #0 in
    let: "b_bal" := ref #0 in
    let: "lk_a" := newlock #() in
    let: "lk_b" := newlock #() in
    (("lk_a", "a_bal"), ("lk_b", "b_bal")).

Definition transfer: val :=
    λ: "bank" "amt",
    let: "a" := Fst "bank" in
    let: "b" := Snd "bank" in
    acquire (Fst "a");;
    acquire (Fst "b");;
    let: "a_bal" := !(Snd "a") in
    let: "b_bal" := !(Snd "b") in
    Snd "a" <- !(Snd "a") - "amt";;
    Snd "b" <- !(Snd "b") + "amt";;
    release (Fst "b");;
    release (Fst "a");;
    #().

Definition check_consistency: val :=
    λ: "bank",
    let: "a" := Fst "bank" in
    let: "b" := Snd "bank" in
    acquire (Fst "a");;
    acquire (Fst "b");;
    let: "a_bal" := !(Snd "a") in
    let: "b_bal" := !(Snd "b") in
    let: "ok" := "a_bal" + "b_ba;" = #0 in
    release (Fst "b");;
    release (Fst "a");;
    "ok".

Definition demo_check_consistency: val :=
    λ: <>,
    let: "bank" := new_bank #() in
    Fork (transfer "bank" #5);;
    check_consistency "bank".

(* Section heap.

Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!inG Σ (ghostR ZO}}.
Let N := nroot.@"bank". *)

(*
Lemma ghost_var_alloc a :
    ⊢ |==> ∃ γ, own γ (●E a) ∗ own γ (◯E a).
Proof.
    iMod (own_alloc (●E a ⋅ ◯E a)) as (γ) "[H1 H2]".
    { apply excl_auth_valid. }
    iModIntro. iExists γ. iFrame.
Qed.

Lemma ghost_var_agree γ a1 a2 :
    own γ (●E a1) -∗ own γ (◯E a2) -∗ ⌜ a1 = a2 ⌝.
Proof using All.
    iIntros "Hy1 Hy2"
    iDestruct (own_valid_2 with "Hy1 Hy2") as "H".
    iDestruct "H" as %<-%excl_auth_agree%leibniz_equiv.
    done.
Qed.

Lemma ghost_var_update {γ} (a1' a1 a2 : A) :
    own γ (●E a1) -∗ own γ (◯E a2) -∗
    |==> own γ (●E a1') ∗ own γ (◯E a1').
Proof.
    iIntros "Hy● Hy◯".
    iMod (own_update_2 _ _ _ (●E a1' ⋅ ◯E a1') with "Hy● Hy◯") as "[$$]".
    { apply excl_auth_update. }
    done.
Qed.


Definition account_inv γ bl_ref : iProp Σ :=
    ∃ (bal: Z), bal_ref ↦ #bal ∗ own γ (◯E bal).

Definition is_account (acct: val) γ : iProp Σ :=
  ∃ (bal_ref: loc) lk,
    ⌜acct = (lk, #bal_ref)%V⌝ ∗
    ∃ (γ1: gname), is_lock γ1 lk (account_inv γ bal_ref).

Definition bank_inv (γ: gname ∗ gname) : iProp Σ :=
∃ (bal1 bal2: Z),
    own γ.1 (●E bal1) ∗
    own γ.2 (●E bal2) ∗
    ⌜(bal1 + bal2)%Z = 0⌝.

 *)
