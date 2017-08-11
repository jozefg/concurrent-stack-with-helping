From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.algebra Require Import agree list.
From iris.heap_lang Require Import assert proofmode notation.
Set Default Proof Using "Type".

Definition mk_stack : val :=
  λ: "_",
  let: "r" := ref NONEV in
  (rec: "pop" "n" :=
     match: !"r" with
       NONE => #-1
     | SOME "hd" =>
       if: CAS "r" (SOME "hd") (Snd "hd")
       then Fst "hd"
       else "pop" "n"
     end,
    rec: "push" "n" :=
       let: "r'" := !"r" in
       let: "r''" := SOME ("n", "r'") in
       if: CAS "r" "r'" "r''"
       then #()
       else "push" "n").

Section stacks.
  Context `{!heapG Σ}.
  Implicit Types l : loc.

  Definition is_stack_pre (P : val → iProp Σ) (F : val -c> iProp Σ) :
     val -c> iProp Σ := λ v,
    (v ≡ NONEV ∨ ∃ (h t : val), v ≡ SOMEV (h, t)%V ∗ P h ∗ ▷ F t)%I.

  Local Instance is_stack_contr (P : val → iProp Σ): Contractive (is_stack_pre P).
  Proof.
    rewrite /is_stack_pre => n f f' Hf v.
    repeat (f_contractive || f_equiv).
    apply Hf.
  Qed.

  Definition is_stack_def (P : val -> iProp Σ) := fixpoint (is_stack_pre P).
  Definition is_stack_aux P : seal (@is_stack_def P). by eexists. Qed.
  Definition is_stack P := unseal (is_stack_aux P).
  Definition is_stack_eq P : @is_stack P = @is_stack_def P := seal_eq (is_stack_aux P).

  Definition stack_inv P v :=
    (∃ l v', ⌜v = #l⌝ ∗ l ↦ v' ∗ is_stack P v')%I.


  Lemma is_stack_unfold (P : val → iProp Σ) v :
      is_stack P v ⊣⊢ is_stack_pre P (is_stack P) v.
  Proof.
    rewrite is_stack_eq. apply (fixpoint_unfold (is_stack_pre P)).
  Qed.

  Lemma is_stack_disj (P : val → iProp Σ) v :
      is_stack P v -∗ is_stack P v ∗ (v ≡ NONEV ∨ ∃ (h t : val), v ≡ SOMEV (h, t)%V).
  Proof.
    iIntros "Hstack".
    iDestruct (is_stack_unfold with "Hstack") as "[#Hstack|Hstack]".
    - iSplit; try iApply is_stack_unfold; iLeft; auto.
    - iDestruct "Hstack" as (h t) "[#Heq rest]".
      iSplitL; try iApply is_stack_unfold; iRight; auto.
  Qed.

  Theorem stack_works P Φ :
    (∀ (f₁ f₂ : val),
            (∀ (v : val), □ WP f₁ #() {{ v, P v  ∨ v ≡ #-1 }})
         -∗ (∀ (v : val), □ (P v -∗ WP f₂ v {{ v, True }}))
         -∗ Φ (f₁, f₂)%V)%I
    -∗ WP mk_stack #()  {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp_lam.
    wp_alloc l as "Hl".
    pose proof (nroot .@ "N") as N.
    rewrite -wp_fupd.
    iMod (inv_alloc N _ (stack_inv P #l) with "[Hl]") as "#Hisstack".
    iExists l, NONEV; iSplit; iFrame; auto.
    { iApply is_stack_unfold. iLeft; auto. }
    wp_let.
    iModIntro.
    iApply "HΦ".
    - iIntros (v) "!#".
      iLöb as "IH".
      wp_rec.
      wp_bind (! #l)%E.
      iInv N as "Hstack" "Hclose".
      iDestruct "Hstack" as (l' v') "[>% [Hl' Hstack]]".
      injection H; intros; subst.
      wp_load.
      iDestruct (is_stack_disj with "Hstack") as "[Hstack #Heq]".
      iMod ("Hclose" with "[Hl' Hstack]").
      iExists l', v'; iFrame; auto.
      iModIntro.
      iDestruct "Heq" as "[H | H]".
      + iRewrite "H".
        wp_match.
        iRight; auto.
      + iDestruct "H" as (h t) "H".
        iRewrite "H".
        assert (to_val (h, t)%V = Some (h, t)%V) by apply to_of_val.
        assert (is_Some (to_val (h, t)%V)) by (exists (h, t)%V; auto).
        wp_match. fold of_val.
        unfold subst; simpl; fold subst.
        wp_bind (CAS _ _ _).
        wp_proj.
        iInv N as "Hstack" "Hclose".
        iDestruct "Hstack" as (l'' v'') "[>% [Hl'' Hstack]]".
        injection H2; intros; subst.
        assert (Decision (v'' = InjRV (h, t)%V)) as Heq by apply val_eq_dec.
        destruct Heq.
        * wp_cas_suc.
          iDestruct (is_stack_unfold with "Hstack") as "[Hstack | Hstack]".
          subst.
          iDestruct "Hstack" as "%"; discriminate.
          iDestruct "Hstack" as (h' t') "[% [HP Hstack]]".
          subst.
          injection H3.
          intros.
          subst.
          iMod ("Hclose" with "[Hl'' Hstack]").
          iExists l'', t'; iFrame; auto.
          iModIntro.
          wp_if.
          wp_proj.
          iLeft; auto.
        * wp_cas_fail.
          iMod ("Hclose" with "[Hl'' Hstack]").
          iExists l'', v''; iFrame; auto.
          iModIntro.
          wp_if.
          iApply "IH".
    - iIntros (v) "!# HP".
      iLöb as "IH".
      wp_rec.
      wp_bind (! _)%E.
      iInv N as "Hstack" "Hclose".
      iDestruct "Hstack" as (l' v') "[>% [Hl' Hstack]]".
      injection H; intros; subst.
      wp_load.
      iMod ("Hclose" with "[Hl' Hstack]").
      by (iExists l', v'; iFrame).
      iModIntro.
      wp_let.
      wp_let.
      wp_bind (CAS _ _ _).
      iInv N as "Hstack" "Hclose".
      iDestruct "Hstack" as (l'' v'') "[>% [Hl'' Hstack]]".
      injection H0; intros; subst.
      assert (Decision (v'' = v'%V)) as Heq by apply val_eq_dec.
      destruct Heq.
      + wp_cas_suc.
        iMod ("Hclose" with "[Hl'' HP Hstack]").
        iExists l'', (InjRV (v, v')%V).
        iFrame; auto.
        iSplit; auto.
        iApply is_stack_unfold.
        iRight.
        iExists v, v'.
        iSplit; auto.
        subst; iFrame.
        iModIntro.
        wp_if.
        done.
      + wp_cas_fail.
        iMod ("Hclose" with "[Hl'' Hstack]").
        iExists l'', v''; iFrame; auto.
        iModIntro.
        wp_if.
        iApply "IH".
        done.
  Qed.
End stacks.
