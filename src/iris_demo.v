(* Authoritative CMRA where the fragment is exclusively owned. This is
effectively a single "ghost variable" with two views, the fragment
◯E a and the authority ●E a.*)
From iris.algebra.lib Require Import excl_auth.
(* Semantic Invariants *)
From iris.base_logic.lib Require Import invariants.
(* Has definition for the notation "e1 ||| e2" *)
From iris.heap_lang Require Import lib.par.
(* HeapLang tactics as in
https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/heap_lang.md *)
From iris.heap_lang Require Import proofmode.
(* Mostly Syntactic sugars for heap_lang?
https://plv.mpi-sws.org/coqdoc/iris/iris.heap_lang.notation.html *)
From iris.heap_lang Require Import notation.
(* This will complete all Proof commands not followed by a using part with
`using "All"`? Not sure what this means really.*)
Set Default Proof Using "All".
(* A notation scope is a set of notations for terms with their interpretations.
Notation scopes p[rovide a weak, purely syntactic form of notation overloading:
a symbol may refer to different definitions depending on which notation scopes
are currently open. For instance, the infix symbol + can be used to refer to
distinct definitions of the addition operator, such as for natural numbers,
integers or reals. Notation scopes can include an interpretation for numbers
and strings with the Number Notation and STring Notation commands. *)
(* Z_scope includes the standard arithmetical operators and relations on type Z
(binary integer numbers). It is delimited by the key Z and comes with an
interpretation for numbers as closed terms of type Z.*)
Open Scope Z.

(* Part 1: verifying swap *)

Definition swap : val := λ: "x" "y",
  let: "tmp" := !"x" in
  "x" <- !"y";;
  "y" <- "tmp".

Section proof.
Context `{!heapGS Σ}.

(* In Coq Hoare Triples are denoted as following
{P} c {Q} meaining
- if command c begins execution in a state satisfying assertion P
- and if c eventually terminates in some final state,
- then that final state will satisfy the assertion Q.

However, the following has only one bracketed part, i don'tknow that it means.*)
Lemma ipm_demo {A} P R (Φ: A → iProp Σ) :
  P ∗ (∃ a, Φ a) ∗ R -∗ ∃ a, Φ a ∗ P.
Proof.
  iIntros "[Hp [HΦ HR]]".
  (* iIntros "H".
  iDestruct "H" as "[HP [HΦ HR]]". *)
  iDestruct "HΦ" as (x) "HΦ".
  iExists x.
  iSplitL "HΦ".
  iAssumption.
  (* Above could be - iAssumption. what is the difference? *)
  iAssumption.
Qed.

Lemma swap_spec x y v1 v2 :
  {{{ x ↦ v1 ∗ y ↦ v2}}} swap #x #y {{{RET #(); x↦v2 ∗ y ↦ v1}}}.
Proof.
  iIntros (Φ) "[Hx Hy] Post".
  unfold swap.
  wp_lam. wp_let.
  wp_load. wp_let.
  wp_load. wp_store.
  wp_store.
  (* After executing above tactic, the goal changes to the following
  |={⊤}=> Φ #()
  What does this mean?
  And after the following tactic iModIntro. the goal changes to
  Φ #()
  Note that iModIntro does the following.
  It introduces a modality in the goal. The typeclass `FromModal` is used to
  specify which modalities this tactic should introduce, and how introducing
  that modality affects the hypotheses. Instances of that type class include:
  later, except 0, basic update and fancy update, intuitionistically,
  persistently, afffinely, plainly, absorbingly, objectively, and subjectively.
  *)
  iModIntro.
  (* iApply pm_trm matches the conclusion of the current goal against the
  conclusion of pm_trm and generates goals for the premises of pm_trm. *)
  iApply "Post".
  iSplitL "Hx".
  - iApply "Hx".
  - iApply "Hy".
Qed.
End proof.

(* Part 2: verifying parallel add 2 example *)
Definition parallel_add : expr :=
  let: "r" := ref #0 in
  (* FAA is fetch-and-add.*)
  (FAA "r" #2 ||| FAA "r" #2);;
  !"r".

Section proof.
  Context `{!heapGS Σ, !spawnG Σ}.

  (* we need to name our invariant; any name will do here *)
  Let N := nroot.@"example".

  Definition  parallel_add_inv (r: loc) :iProp Σ :=
    (∃ n: Z, r ↦ #n ∗ ⌜ Zeven n ⌝)%I.

  (* main body of the proof *)
  Lemma faa_preserves_even (r: loc) :
  {{{ inv N (parallel_add_inv r) }}}
    FAA #r #2
  {{{ (n: Z), RET #n; True }}}.
  Proof.
    (* Why is #Hinv listed as Hinv in the precondition? *)
    iIntros (Φ) "#Hinv Post".
    (* `iInv H as (x1 ... xn) "ipat"`
    Opens an invariant in hypothesis H. The result is destructed using Coq intro
    patterns x1 ... xn (for existential quantifiers) and then the proof mode
    introduction pattern ipat.
    `> ipat`
    Eliminates a modality (if the goal permits); commonly used to strip a lter
    from the hypothesis when it is timeless and the goal is either a `WP` or
    an update modality `|={E}=>`.
    *)
    iInv "Hinv" as (n) ">[Hr %]".
    wp_faa.
    iModIntro.
    (* `iSplitL "H1 ... Hn"`
    Split a conjuction P ∗ Q into two proofs. The hypotheses `H1 ... Hn` are
    used for the left conjunct, and the remaining ones for the right conjunct.*)
    iSplitL "Hr".
    { iNext. iExists (n+2). iFrame.
      (* `iPureIntro`: turn a pure goal, typically of the form ⌜φ ⌝, into a Coq
      goal. This tactic also works for goals of the shape `a ≡ b` on discrete
      OFEs, and  `✓ a` on discrete cameras.*)
      iPureIntro.
      (* `apply term`: a Coq tactic. This tactic applies to any goal. The tactic
      `apply` tries to match the current goal against the conclusion of the type
      of `term`. If it succeeds, then the tactic returns as many subgoals as the
      number of non-dependent premises of the type term. *)
      (* Zeven_plus_Zeven is a theorem in Coq's Z_scope.
      Theorem Zeven_plus_Zeven a b : Zeven a -> Zeven b -> Zeven (a+b). *)
      apply Zeven_plus_Zeven; done. }
    by iApply "Post".
  Qed.

  Lemma paralle_add_spec_even :
    {{{ True }}} parallel_add {{{ n, RET #n; ⌜Zeven n⌝ }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add.
    wp_alloc r as "Hr".
    wp_let.
    iMod (inv_alloc N _ (parallel_add_inv r) with "[Hr]") as "#Hinv".
    { iNext. unfold parallel_add_inv.
    iExists 0. iFrame. }
    wp_smart_apply (wp_par (λ _, True%I) (λ _, True%I)).
    { (* first thread *)
      wp_apply (faa_preserves_even with "[$Hinv]").
      done.
    }
    { (* second thread *)
      wp_apply (faa_preserves_even with "[$Hinv]").
      done.
    }

    iIntros (??) "_".
    iNext.
    wp_pures.
    iInv "Hinv" as (n) ">[Hr %]".
    wp_load.
    iModIntro.
    iSplitL "Hr".
    (* What is the difference between iFrame and by iFrame?*)
    {
      iExists _; by iFrame.
    }
    iApply "Post".
    done.
  Qed.
End proof.

  (* Part 3 verifying parallel add returns 4*)
Section proof.
  (* What does this mean? *)
  (* Definition excl_authR (A: ofe) cmra :=
      authR (optionUR) (exclR A)).
  *)
  Context `{!heapGS Σ, !spawnG Σ, !inG Σ (excl_authR ZO)}.

  Let N := nroot.@"example2".

  Definition parallel_add_inv_2 (r: loc) (γ1 γ2 : gname) : iProp Σ :=
    ∃ (n1 n2 : Z),
      r ↦ #(n1+n2) ∗ own γ1 (●E n1) ∗ own γ2 (●E n2).


  Lemma ghost_var_alloc (n: Z) :
    (* How do you read this? *)
    True ==∗ ∃ γ, own γ (●E n) ∗ own γ (◯E n).
  Proof.
    iIntros "_".
    iMod (own_alloc (●E n ⋅ ◯E n)) as (γ) "[H● H◯]".
    (* What does excl_auth_valid do? *)
    { apply excl_auth_valid. }
    iModIntro.
    iExists _; iFrame.
  Qed.

  Lemma ghost_var_agree (γ: gname) (n1 n2 : Z) :
    own γ (●E n1) ∗ own γ (◯E n2) -∗ ⌜n1 = n2⌝.
  Proof.
    iIntros "[H1 H2]".
    iDestruct (own_op with "[$H1 $H2]") as "H".

    iDestruct (own_valid with "H") as %H.
    apply excl_auth_agree_L in H; done.
  Qed.

  Lemma ghost_var_update (n': Z) (γ: gname) (n: Z) :
    own γ (●E n) ∗ own γ (◯E n) ==∗ own γ (●E n') ∗ own γ (◯E n').
  Proof.
    iIntros "[H1 H2]".
    iDestruct (own_op with "[$H1 $H2]") as "H".
    iMod (own_update _ _ (●E n' ⋅ ◯E n') with "H") as "[H1 H2]".
    {apply excl_auth_update. }
    by iFrame.
  Qed.

  Lemma parallel_add_spec :
    {{{ True }}} parallel_add {{{ n, RET #n; ⌜n = 4⌝ }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add.
    wp_alloc r as "Hr".
    wp_let.
    iMod (ghost_var_alloc 0 with "[//]") as (γ1) "[Hγ1● Hγ1◯]".
    iMod (ghost_var_alloc 0 with "[//]") as (γ2) "[Hγ2● Hγ2◯]".
    iMod (inv_alloc N _ (parallel_add_inv_2 r γ1 γ2  ) with "[Hr Hγ1● Hγ2●]")
      as "#Hinv".
    { iNext. iExists _, _; iFrame. }
    wp_smart_apply (wp_par (λ _, own γ1 (◯E 2))%I (λ _, own γ2 (◯E 2))%I with
      "[Hγ1◯] [Hγ2◯]").
    { iInv "Hinv" as (n1 n2) ">(Hr & Hγ1 & Hγ2)".
      wp_faa.
      iDestruct (ghost_var_agree with "[$Hγ1 $Hγ1◯]") as %->.
      iMod (ghost_var_update 2 with "[$Hγ1 $Hγ1◯]") as "[Hγ1 Hγ1◯]".
      iFrame "Hγ1◯".
      iModIntro. iNext. iExists _, _. iFrame.
      replace (2+n2) with (0+n2+2) by lia.
      iAssumption.
    }
    { iInv "Hinv" as (n1 n2) ">(Hr & Hγ1 & Hγ2)".
      wp_faa.
      iDestruct (ghost_var_agree with "[$Hγ2 $Hγ2◯]") as %->.
      iMod (ghost_var_update 2 with "[$Hγ2 $Hγ2◯]") as "[Hγ2 Hγ2◯]".
      iFrame "Hγ2◯".
      iModIntro. iNext. iExists _, _. iFrame.
      replace (n1+2) with (n1+0+2) by lia.
      iAssumption.
    }
    iIntros (v1 v2) "[Hγ1◯ Hγ2◯] !>".
    wp_seq.
    iInv "Hinv" as (n1 n2) ">(Hr & Hγ1 & Hγ2)".
    iDestruct (ghost_var_agree with "[$Hγ1 $Hγ1◯]") as %->.
    iDestruct (ghost_var_agree with "[$Hγ2 $Hγ2◯]") as %->.
    wp_load.
    iModIntro.
    iSplitL "Hr Hγ1 Hγ2".
    { iNext. iExists _, _; iFrame. }
    iApply "Post".
    done.
  Qed.
End proof.

