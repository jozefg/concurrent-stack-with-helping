From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang proofmode notation.
From iris.algebra Require Import excl.
Set Default Proof Using "Type".

Definition mk_stack : val :=
  λ: "_",
  let: "r" := ref NONEV in
  (rec: "pop" "n" :=
       (match: !"r" with
          NONE => NONE
        | SOME "hd" =>
          if: CAS "r" (SOME "hd") (Snd "hd")
          then SOME (Fst "hd")
          else "pop" "n"
        end),
    rec: "push" "n" :=
        let: "r'" := !"r" in
        let: "r''" := SOME ("n", "r'") in
        if: CAS "r" "r'" "r''"
        then #()
        else "push" "n").

Section stack_works.
  Context `{!heapG Σ}.
  Implicit Types l : loc.

  Fixpoint is_stack xs v : iProp Σ :=
    (match xs with
     | [] => ⌜v = NONEV⌝
     | x :: xs => ∃ (t : val), ⌜v = SOMEV (x, t)%V⌝ ∗ is_stack xs t
     end)%I.

  Definition stack_inv P v :=
    (∃ l v' xs, ⌜v = #l⌝ ∗ l ↦ v' ∗ is_stack xs v' ∗ P xs)%I.

  Lemma is_stack_disj xs v :
      is_stack xs v -∗ is_stack xs v ∗ (⌜v = NONEV⌝ ∨ ∃ (h t : val), ⌜v = SOMEV (h, t)%V⌝).
  Proof.
    iIntros "Hstack".
    destruct xs.
    - iSplit; try iLeft; auto.
    - iSplit; auto; iRight; iDestruct "Hstack" as (t) "[% Hstack]";
      iExists v0, t; auto.
  Qed.

  Lemma is_stack_uniq : ∀ xs ys v,
      is_stack xs v ∗ is_stack ys v -∗ ⌜xs = ys⌝.
  Proof.
    induction xs, ys; iIntros (v') "[Hstack1 Hstack2]"; auto.
    - iDestruct "Hstack1" as "%".
      iDestruct "Hstack2" as (t) "[% Hstack2]".
      subst.
      discriminate.
    - iDestruct "Hstack2" as "%".
      iDestruct "Hstack1" as (t) "[% Hstack1]".
      subst.
      discriminate.
    - iDestruct "Hstack1" as (t) "[% Hstack1]".
      iDestruct "Hstack2" as (t') "[% Hstack2]".
      subst; injection H0; intros; subst.
      iDestruct (IHxs with "[Hstack1 Hstack2]") as "%".
        by iSplitL "Hstack1".
      subst; auto.
  Qed.

  Lemma is_stack_empty : ∀ xs,
      is_stack xs (InjLV #()) -∗ ⌜xs = []⌝.
  Proof.
    iIntros (xs) "Hstack".
    destruct xs; auto.
    iDestruct "Hstack" as (t) "[% rest]".
    discriminate.
  Qed.
  Lemma is_stack_cons : ∀ xs h t,
      is_stack xs (InjRV (h, t)%V) -∗
               is_stack xs (InjRV (h, t)%V) ∗ ∃ ys, ⌜xs = h :: ys⌝.
  Proof.
    destruct xs; iIntros (h t) "Hstack".
    - iDestruct "Hstack" as "%"; discriminate.
    - iSplit; [auto | iExists xs].
      iDestruct "Hstack" as (t') "[% Hstack]".
      injection H; intros; subst; auto.
  Qed.

  Theorem stack_works P Q Q' Q'' Φ :
    (∀ (f₁ f₂ : val) ι,
        (□((∀ v vs, P (v :: vs) ={⊤∖↑ι}=∗ Q v ∗ P vs) -∗
            (P [] ={⊤∖↑ι}=∗ Q' ∗ P []) -∗
            WP f₁ #() {{ v, (∃ (v' : val), v ≡ SOMEV v' ∗ Q v') ∨ (v ≡ NONEV ∗ Q')}}))
         -∗ (∀ (v : val),
               □ ((∀ vs, P vs ={⊤∖↑ι}=∗ P (v :: vs) ∗ Q'') -∗
                  WP f₂ v {{ v, Q'' }}))
         -∗ Φ (f₁, f₂)%V)%I
    -∗ P []
    -∗ WP mk_stack #()  {{ Φ }}.
  Proof.
    iIntros "HΦ HP".
    pose proof (nroot .@ "N") as N.
    wp_let.
    wp_alloc l as "Hl".
    iMod (inv_alloc N _ (stack_inv P #l) with "[Hl HP]") as "#Istack".
    { iNext; iExists l, (InjLV #()), []; iSplit; iFrame; auto. }
    wp_let.
    iApply "HΦ".
    - iIntros "!# Hsucc Hfail".
      iLöb as "IH".
      wp_rec.
      wp_bind (! _)%E.
      iInv N as "Hstack" "Hclose".
      iDestruct "Hstack" as (l' v' xs) "[>% [Hl' [Hstack HP]]]".
      injection H; intros; subst.
      wp_load.
      iDestruct (is_stack_disj with "[Hstack]") as "[Hstack H]"; auto.
      iDestruct "H" as "[% | H]".
      * subst.
        iDestruct (is_stack_empty with "Hstack") as "%".
        subst.
        iMod ("Hfail" with "HP") as "[HQ' HP]".
        iMod ("Hclose" with "[Hl' Hstack HP]").
        { iExists l', (InjLV #()), []; iSplit; iFrame; auto. }
        iModIntro.
        wp_match.
        iRight; auto.
      * iDestruct "H" as (h t) "%".
        subst.
        iMod ("Hclose" with "[Hl' Hstack HP]").
        { iExists l', (InjRV (h, t)), xs; iSplit; iFrame; auto. }
        iModIntro.

        assert (to_val (h, t)%V = Some (h, t)%V) by apply to_of_val.
        assert (is_Some (to_val (h, t)%V)) by (exists (h, t)%V; auto).
        wp_match.
        unfold subst; simpl; fold of_val.

        wp_proj.
        wp_bind (CAS _ _ _).
        iInv N as "Hstack" "Hclose".
        iDestruct "Hstack" as (l'' v' ys) "[>% [Hl'' [Hstack HP]]]".
        injection H2; intros; subst.
        assert (Decision (v' = InjRV (h, t)%V)) as Heq by apply val_eq_dec.
        destruct Heq.
      + wp_cas_suc.
        subst.
        iDestruct (is_stack_cons with "Hstack") as "[Hstack H]".
        iDestruct "H" as (ys') "%"; subst.
        iDestruct "Hstack" as (t') "[% Hstack]".
        injection H3; intros; subst.
        iDestruct ("Hsucc" with "[HP]") as "> [HQ HP]"; auto.
        iMod ("Hclose" with "[Hl'' Hstack HP]").
        { iExists l'', t', ys'; iSplit; iFrame; auto. }
        iModIntro.
        wp_if.
        wp_proj.
        iLeft; iExists h; auto.
      + wp_cas_fail.
        iMod ("Hclose" with "[Hl'' Hstack HP]").
        { iExists l'', v', ys; iSplit; iFrame; auto. }
        iModIntro.
        wp_if.
        iApply ("IH" with "Hsucc Hfail").
    - iIntros (v) "!# Hpush".
      iLöb as "IH".
      wp_rec.
      wp_bind (! _)%E.
      iInv N as "Hstack" "Hclose".
      iDestruct "Hstack" as (l' v' ys) "[>% [Hl' [Hstack HP]]]".
      injection H; intros; subst.
      wp_load.
      iMod ("Hclose" with "[Hl' Hstack HP]").
      { iExists l', v', ys; iSplit; iFrame; auto. }
      iModIntro.
      wp_let.
      wp_let.
      wp_bind (CAS _ _ _).
      iInv N as "Hstack" "Hclose".
      iDestruct "Hstack" as (l'' v'' xs) "[>% [Hl'' [Hstack HP]]]".
      injection H0; intros; subst.
      assert (Decision (v' = v''%V)) as Heq by apply val_eq_dec.
      destruct Heq.
      + wp_cas_suc.
        iDestruct ("Hpush" with "[HP]") as "> [HP HQ]"; auto.
        iMod ("Hclose" with "[Hl'' Hstack HP]").
        { iExists l'', (InjRV (v, v')), (v :: xs); iSplit; iFrame; auto.
          iExists v'; iSplit; subst; auto. }
        iModIntro.
        wp_if.
        done.
      + wp_cas_fail.
        iMod ("Hclose" with "[Hl'' Hstack HP]").
        { iExists l'', v'', xs; iSplit; iFrame; auto. }
        iModIntro.
        wp_if.
        iApply ("IH" with "Hpush").
  Qed.
End stack_works.
