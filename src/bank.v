(*! A simple demo of Iris and Coq following tchajed/iris-bank-demo and article
https://plv.csail.mit.edu/blog/iris-intro.html *)

From iris.base_logic Require Import lib.ghost_var.

(* This code is written in HeapLang, a simple ML-like language shipped with
Iris. *)
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

Section heap.

(* mostly standard boilerplate *)
Context `{!heapGS Σ}.
Context `{!lockG Σ}.
Context `{!ghost_varG Σ Z}.
Let N := nroot.@"bank".


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
*)

(** Verifying concurrent software generally require the use of _ghost_state_.
variables that are introduced into the program only for the sake of the proof.
In some systems (like Dafny or VeriFast), ghost variables actually show up in
the source code for the program being verified. In Iris, we'll only see ghost
variables in the proof.

We'll now start writing down the invariant for this proof, and this is where
we'll reference the ghost variables. We do that with a proposition [ghost_var γ
q v], which says that the ghost variable with name [gamma] has value [v], and we
own a fraction [q] (≤1) of it. Ghost variables in Iris are always a combination
of knowledge about the variable and ownership over it. The key idea is that to
change a ghost variable we need to assemble all the pieces of it, adding up to
a fraction of 1; this guarantees that no other thread is claiming ownership and
makes it sound to change its value without invalidating over thread's proofs. *)

(** account_inv is the lock invariant associated with each account. It exposes a
ghost name [γ] used to tie the account balance to a ghost variable. In the lock
invariant we'll claim half ownership, while the other half will be in a
system-wide invariant; this lets us reference the variable's value from both
places and also assert that the lock is needed to change this balance. *)
Definition account_inv γ bal_ref : iProp Σ :=
    ∃ (bal: Z), bal_ref ↦ #bal ∗ ghost_var γ (1/2) bal.

(** an account is a pair of a lock and an account protected by the lock *)
Definition is_account (acct: val) γ : iProp Σ :=
    ∃ (bal_ref: loc) lk,
        ⌜acct = (lk, #bal_ref)%V⌝ ∗
        (* The important part of [is_lock] is the lock invariant, expressed as
        an arbitrary Iris proposition [iProp Σ]. The idea of lock invariants is
        that first we associate a lock invariant [P] with the lock (we're doing
        that here). Then when we acquire the lock we get (resources satisfying)
        [P], and when we release it we have to give back (resources satisfying)
        [P]. Crucially during the critical section we have access to [P] and can
        violate this proposition freely. *)
        ∃ (γ1: gname), is_lock γ1 lk (account_inv γ bal_ref).

(* Not sure how I could differentiate * and ∗ in the following *)
(** bank_inv is the invariant (the usual one that holds at all intermediate
points) that holds the authoritative fragments for the account balances and
importantly states that they are always equal. Any thread can open the invariant
to "read" the logical balances, but modifications must respect the constraint
here.

We need to say where th logical (ghost) account balances are stored so this
definition also takes two ghost names.

As mentioned above, we claim half ownership to reference the value of both ghost
variables. This half is a bit different because it's in a regular invariant,
so any thread can open this invariant to learn the logical balances sum to
zero. *)
Definition bank_inv (γ: gname * gname) : iProp Σ :=
    ∃ (bal1 bal2: Z),
        ghost_var γ.1 (1/2) bal1 ∗
        ghost_var γ.2 (1/2) bal2 ∗
        ⌜(bal1 + bal2)%Z = 0⌝.

(** finally [is_bank] ties everything together, the accounts and invariant *)
Definition is_bank (b: val): iProp Σ :=
    ∃ (acct1 acct2:val) (γ: gname*gname),
    ⌜b = (acct1, acct2)%V⌝ ∗
    is_account acct1 γ.1 ∗
    is_account acct2 γ.2 ∗
    inv N (bank_inv γ).

(* Imporantly [is_bank b] is _persistent_, which means we can share it among
threads. We'l see this used in [wp_demo_check_consistency].

This proofs goes through because the componenets of [is_bank] are persistent.
These include the pure facts (it should be intuitive that these are persistent,
since they don't talk about resources at all), the invariant (because [inv N P]
is just knowledge of an invariant, which can and should be shared) and
[is_lock yl lk p] (similarly, this is knowledge that there is a lock at lk and
is shareable). *)
Instance is_bank_Persistent b : Persistent (is_bank b).
Proof. apply _. (* this proof is actually automatic *) Qed.

(* [new_bank] is actually interesting because we have to create all the ghost
state, lock invariants, and invariant, and of course when you create an
invariant holding [P] you have to prove [P].

These ghost operations correspond to [iMod] in these proofs, which use theorems
with [|==>] and [==∗]. *)
Theorem wp_new_bank :
    (* This is a Hoare triple using Iris' program logic. *)
    {{{ True }}}
        new_bank #()
        (* the [b,] part is a shorthand for [∃ b, ...] in the postcondition, and
        [RET b] says the function returns b. *)
    {{{ b, RET b; is_bank b }}}.
Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec. (* unfold new_bank and runs a step of reduction *)
    wp_alloc a_ref as "Ha".
    wp_alloc b_ref as "Hb".
    (* The first interesting step of the proof is that we execute the ghost
    variable change in [ghost_var_alloc] and at the same time destruct it with
    [as (γ1) "(Hown1&Hγ1)"], using [γ1] for the ghost name and [Hown1] and
    [Hγ1] for the two halves, respectively. *)
    iMod (ghost_var_alloc 0) as (γ1) "(Hown1&Hγ1)".
    wp_pures.
    (* Now we can initialize the lock invariant for the first acount, which
    will own the auth ["Hγ1"] created above. *)
    wp_apply (newlock_spec (account_inv γ1 a_ref) with "[Ha Hγ1]").
    { iExists _; iFrame. }
    iIntros (lk_a γlk1) "Hlk1".
    iMod (ghost_var_alloc 0) as (γ2) "(Hown2&Hγ2)".
    wp_pures.
    wp_apply (newlock_spec (account_inv γ2 b_ref) with "[Hb Hγ2]").
    { iExists _; iFrame. }
    iIntros (lk_b γlk2) "Hlk2".
    wp_pures.
    iMod (inv_alloc N _ (bank_inv (γ1, γ2)) with "[Hown1 Hown2]") as "Hinv".
    { iNext. iExists _, _; iFrame.
      iPureIntro; auto. }
    iModIntro.
    iApply "HΦ".
    iExists _, _, (γ1, γ2); iFrame.
    iSplit; first eauto.
    simpl.
    iSplitL "Hlk1".
    - iExists _; eauto with iFrame.
    - iExists _; eauto with iFrame.
Qed.


End heap.
