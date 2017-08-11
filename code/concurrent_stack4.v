From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang proofmode notation.
From iris.algebra Require Import excl.
Set Default Proof Using "Type".

Definition hidden_eq {A} (n m : A) := n = m.

Definition mk_offer : val :=
  λ: "v", ("v", ref #0).
Definition revoke_offer : val :=
  λ: "v", if: CAS (Snd "v") #0 #2 then SOME (Fst "v") else NONE.
Definition take_offer : val :=
  λ: "v", if: CAS (Snd "v") #0 #1 then SOME (Fst "v") else NONE.

Definition mailbox : val :=
  λ: "_",
  let: "r" := ref NONEV in
  (rec: "put" "v" :=
     let: "off" := mk_offer "v" in
     "r" <- SOME "off";;
     revoke_offer "off",
   rec: "get" "n" :=
     let: "offopt" := !"r" in
     match: "offopt" with
       NONE => NONE
     | SOME "x" => if: CAS (Snd "x") #0 #1 then SOME (Fst "x") else NONE
     end
  ).

Definition mk_stack : val :=
  λ: "_",
  let: "mailbox" := mailbox #() in
  let: "put" := Fst "mailbox" in
  let: "get" := Snd "mailbox" in
  let: "r" := ref NONEV in
  (rec: "pop" "n" :=
     match: "get" #() with
       NONE =>
       (match: !"r" with
          NONE => NONE
        | SOME "hd" =>
          if: CAS "r" (SOME "hd") (Snd "hd")
          then SOME (Fst "hd")
          else "pop" "n"
        end)
     | SOME "x" => SOME "x"
     end,
    rec: "push" "n" :=
      match: "put" "n" with
        NONE => #()
      | SOME "n" =>
        let: "r'" := !"r" in
        let: "r''" := SOME ("n", "r'") in
        if: CAS "r" "r'" "r''"
        then #()
        else "push" "n"
      end).

Definition channelR := exclR unitR.
Class channelG Σ := { channel_inG :> inG Σ channelR }.
Definition channelΣ : gFunctors := #[GFunctor channelR].
Instance subG_channelΣ {Σ} : subG channelΣ Σ → channelG Σ.
Proof. solve_inG. Qed.

Section side_channel.
  Context `{!heapG Σ, !channelG Σ}.
  Implicit Types l : loc.

  Definition stages γ (P : list val → iProp Σ) (Q : iProp Σ) l (v : val):=
    ((l ↦ #0 ∗ (∀ vs, P vs ==∗ P (v :: vs) ∗ Q))
     ∨ (l ↦ #1 ∗ Q)
     ∨ (l ↦ #1 ∗ own γ (Excl ()))
     ∨ (l ↦ #2 ∗ own γ (Excl ())))%I.

  Definition is_offer ι' γ (P : list val → iProp Σ) Q (v : val) : iProp Σ :=
    (∃ v' l, ⌜v = (v', #l)%V⌝ ∗ ∃ ι, ⌜ι' ⊥ ι⌝ ∗ inv ι (stages γ P Q l v'))%I.

  Definition mailbox_inv ι (P : list val → iProp Σ) Q (v : val) : iProp Σ :=
    (∃ l, ⌜v = #l⌝ ∗ (l ↦ NONEV ∨ (∃ v' γ, l ↦ SOMEV v' ∗ is_offer ι γ P Q v')))%I.
End side_channel.
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

  Theorem stack_works {channelG0 : channelG Σ} P Q Q' Q'' Φ :
    (∀ (f₁ f₂ : val),
        (□((∀ v vs, P (v :: vs) ==∗ Q v ∗ P vs) -∗
            (P [] ==∗ Q' ∗ P []) -∗
            WP f₁ #() {{ v, (∃ (v' : val), v ≡ SOMEV v' ∗ Q v') ∨ (v ≡ NONEV ∗ Q')}}))
         -∗ (∀ (v : val),
               □ ((∀ vs, P vs ==∗ P (v :: vs) ∗ Q'') -∗ WP f₂ v {{ v, Q'' }}))
         -∗ Φ (f₁, f₂)%V)%I
    -∗ P []
    -∗ WP mk_stack #()  {{ Φ }}.
  Proof.
    iIntros "HΦ HP".
    assert (exists n : namespace, hidden_eq n (nroot .@ "N")) as H
        by (exists (nroot .@ "N"); unfold hidden_eq; auto).
    destruct H as (N, Neq).
    assert (exists n : namespace, hidden_eq n (nroot .@ "N'")) as H
        by (exists (nroot .@ "N'"); unfold hidden_eq; auto).
    destruct H as (N', N'eq).
    wp_let.
    wp_let.
    wp_alloc m as "Hm".
    iMod (inv_alloc N' _ (mailbox_inv N P Q'' #m) with "[Hm]") as "#Imailbox".
    iExists m; iSplit; auto.
    wp_let.
    wp_let.
    wp_proj.
    wp_let.
    wp_proj.
    wp_let.
    wp_alloc l as "Hl".
    iMod (inv_alloc N _ (stack_inv P #l) with "[Hl HP]") as "#Istack".
    { iNext; iExists l, (InjLV #()), []; iSplit; iFrame; auto. }
    wp_let.
    iApply "HΦ".
    - iIntros "!# Hsucc Hfail".
      iLöb as "IH".
      wp_rec.
      wp_rec.
      wp_bind (! _)%E.
      iInv N' as "Hmail" "Hclose".
      iDestruct "Hmail" as (m') "[>% H]".
      injection H; intros; subst.
      iDestruct "H" as "[Hm' | H]".
      * wp_load.
        iMod ("Hclose" with "[Hm']").
        { iExists m'; iSplit; auto. }
        iModIntro.
        wp_let.
        wp_match.
        wp_match.
        wp_bind (! _)%E.
        iInv N as "Hstack" "Hclose".
        iDestruct "Hstack" as (l' v' xs) "[>% [Hl' [Hstack HP]]]".
        injection H0; intros; subst.
        wp_load.
        iDestruct (is_stack_disj with "[Hstack]") as "[Hstack H]"; auto.
        iDestruct "H" as "[% | H]".
        + subst.
          iDestruct (is_stack_empty with "Hstack") as "%".
          subst.
          iMod ("Hfail" with "HP") as "[HQ' HP]".
          iMod ("Hclose" with "[Hl' Hstack HP]").
          { iExists l', (InjLV #()), []; iSplit; iFrame; auto. }
          iModIntro.
          wp_match.
          iRight; auto.
        + iDestruct "H" as (h t) "%".
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
          injection H3; intros; subst.
          assert (Decision (v' = InjRV (h, t)%V)) as Heq by apply val_eq_dec.
          destruct Heq.
          ++ wp_cas_suc.
             subst.
             iDestruct (is_stack_cons with "Hstack") as "[Hstack H]".
             iDestruct "H" as (ys') "%"; subst.
             iDestruct "Hstack" as (t') "[% Hstack]".
             injection H4; intros; subst.
             iDestruct ("Hsucc" with "[HP]") as "> [HQ HP]"; auto.
             iMod ("Hclose" with "[Hl'' Hstack HP]").
             { iExists l'', t', ys'; iSplit; iFrame; auto. }
             iModIntro.
             wp_if.
             wp_proj.
             iLeft; iExists h; auto.
          ++ wp_cas_fail.
             iMod ("Hclose" with "[Hl'' Hstack HP]").
             { iExists l'', v', ys; iSplit; iFrame; auto. }
             iModIntro.
             wp_if.
             iApply ("IH" with "Hsucc Hfail").
      * iDestruct "H" as (v' γ') "[Hm' Hoffer]".
        wp_load.
        iDestruct "Hoffer" as (v'' l') "[% #Hoffer]".
        iMod ("Hclose" with "[Hm' Hoffer]").
        { iExists m'. iSplit; auto; iRight.
          iExists v', γ'; iFrame. iExists v'', l'; iSplit; auto. }
        iModIntro.
        wp_let.
        wp_match.
        unfold take_offer.
        subst.
        wp_proj.
        iDestruct "Hoffer" as (ι) "[% Hstages]".
        wp_bind (CAS _ _ _).
        iInv ι as "Hstage" "Hclose".
        iDestruct "Hstage" as "[H | [H | [H | H]]]".
        + iDestruct "H" as "[Hl' Hmove]".
          iInv N as "Hstack" "Hclose2".
          wp_cas_suc.
          iDestruct "Hstack" as (l'' v' xs) "[% [Hl'' [Hstack HP]]]".
          iDestruct ("Hmove" with "HP") as "> [HP HQ'']".
          iDestruct ("Hsucc" with "HP") as "> [HQ HP]".
          iMod ("Hclose2" with "[Hl'' Hstack HP]").
          { iExists l'', v', xs; iSplit; iFrame; auto. }
          iModIntro.
          iMod ("Hclose" with "[Hl' HQ'']").
          { iRight; iLeft; iFrame. }
          iModIntro.
          wp_if.
          wp_proj.

          assert (to_val v'' = Some v'') by apply to_of_val.
          assert (is_Some (to_val v'')) by (exists v''; auto).
          assert (to_val (InjRV v'') = Some (InjRV v'')) by apply to_of_val.
          assert (is_Some (to_val (InjRV v''))) by (exists (InjRV v''); auto).
          wp_match.
          iLeft; iExists v''; iFrame; auto.
        + iDestruct "H" as "[Hl' HQ'']".
          wp_cas_fail.
          iMod ("Hclose" with "[Hl' HQ'']").
          { iRight; iLeft; iFrame. }
          iModIntro.
          wp_if.
          wp_match.
          wp_bind (! _)%E.
          iInv N as "Hstack" "Hclose".
          iDestruct "Hstack" as (l'' v''' xs) "[>% [Hl' [Hstack HP]]]".
          injection H1; intros; subst.
          wp_load.
          iDestruct (is_stack_disj with "[Hstack]") as "[Hstack H]"; auto.
          iDestruct "H" as "[% | H]".
          ** subst.
             iDestruct (is_stack_empty with "Hstack") as "%".
             subst.
             iMod ("Hfail" with "HP") as "[HQ' HP]".
             iMod ("Hclose" with "[Hl' Hstack HP]").
             { iExists l'', (InjLV #()), []; iSplit; iFrame; auto. }
             iModIntro.
             wp_match.
             iRight; auto.
          ** iDestruct "H" as (h t) "%".
             subst.
             iMod ("Hclose" with "[Hl' Hstack HP]").
             { iExists l'', (InjRV (h, t)), xs; iSplit; iFrame; auto. }
             iModIntro.

             assert (to_val (h, t)%V = Some (h, t)%V) by apply to_of_val.
             assert (is_Some (to_val (h, t)%V)) by (exists (h, t)%V; auto).
             wp_match.
             unfold subst; simpl; fold of_val.

             wp_proj.
             wp_bind (CAS _ _ _).
             iInv N as "Hstack" "Hclose".
             iDestruct "Hstack" as (l''' v''' ys) "[>% [Hl''' [Hstack HP]]]".
             injection H4; intros; subst.
             assert (Decision (v''' = InjRV (h, t)%V)) as Heq by apply val_eq_dec.
             destruct Heq.
             ++ wp_cas_suc.
                subst.
                iDestruct (is_stack_cons with "Hstack") as "[Hstack H]".
                iDestruct "H" as (ys') "%"; subst.
                iDestruct "Hstack" as (t') "[% Hstack]".
                injection H5; intros; subst.
                iDestruct ("Hsucc" with "[HP]") as "> [HQ HP]"; auto.
                iMod ("Hclose" with "[Hl''' Hstack HP]").
                { iExists l''', t', ys'; iSplit; iFrame; auto. }
                iModIntro.
                wp_if.
                wp_proj.
                iLeft; iExists h; auto.
             ++ wp_cas_fail.
                iMod ("Hclose" with "[Hl''' Hstack HP]").
                { iExists l''', v''', ys; iSplit; iFrame; auto. }
                iModIntro.
                wp_if.
                iApply ("IH" with "Hsucc Hfail").
        + iDestruct "H" as "[Hl' Hγ']".
          wp_cas_fail.
          iMod ("Hclose" with "[Hl' Hγ']").
          { iRight; iRight; iLeft; iFrame. }
          iModIntro.
          wp_if.
          wp_match.
          wp_bind (! _)%E.
          iInv N as "Hstack" "Hclose".
          iDestruct "Hstack" as (l'' v''' xs) "[>% [Hl' [Hstack HP]]]".
          injection H1; intros; subst.
          wp_load.
          iDestruct (is_stack_disj with "[Hstack]") as "[Hstack H]"; auto.
          iDestruct "H" as "[% | H]".
          ** subst.
             iDestruct (is_stack_empty with "Hstack") as "%".
             subst.
             iMod ("Hfail" with "HP") as "[HQ' HP]".
             iMod ("Hclose" with "[Hl' Hstack HP]").
             { iExists l'', (InjLV #()), []; iSplit; iFrame; auto. }
             iModIntro.
             wp_match.
             iRight; auto.
          ** iDestruct "H" as (h t) "%".
             subst.
             iMod ("Hclose" with "[Hl' Hstack HP]").
             { iExists l'', (InjRV (h, t)), xs; iSplit; iFrame; auto. }
             iModIntro.

             assert (to_val (h, t)%V = Some (h, t)%V) by apply to_of_val.
             assert (is_Some (to_val (h, t)%V)) by (exists (h, t)%V; auto).
             wp_match.
             unfold subst; simpl; fold of_val.

             wp_proj.
             wp_bind (CAS _ _ _).
             iInv N as "Hstack" "Hclose".
             iDestruct "Hstack" as (l''' v''' ys) "[>% [Hl''' [Hstack HP]]]".
             injection H4; intros; subst.
             assert (Decision (v''' = InjRV (h, t)%V)) as Heq by apply val_eq_dec.
             destruct Heq.
             ++ wp_cas_suc.
                subst.
                iDestruct (is_stack_cons with "Hstack") as "[Hstack H]".
                iDestruct "H" as (ys') "%"; subst.
                iDestruct "Hstack" as (t') "[% Hstack]".
                injection H5; intros; subst.
                iDestruct ("Hsucc" with "[HP]") as "> [HQ HP]"; auto.
                iMod ("Hclose" with "[Hl''' Hstack HP]").
                { iExists l''', t', ys'; iSplit; iFrame; auto. }
                iModIntro.
                wp_if.
                wp_proj.
                iLeft; iExists h; auto.
             ++ wp_cas_fail.
                iMod ("Hclose" with "[Hl''' Hstack HP]").
                { iExists l''', v''', ys; iSplit; iFrame; auto. }
                iModIntro.
                wp_if.
                iApply ("IH" with "Hsucc Hfail").

        + iDestruct "H" as "[Hl' Hγ']".
          wp_cas_fail.
          iMod ("Hclose" with "[Hl' Hγ']").
          { iRight; iRight; iRight; iFrame. }
          iModIntro.
          wp_if.
          wp_match.
          wp_bind (! _)%E.
          iInv N as "Hstack" "Hclose".
          iDestruct "Hstack" as (l'' v''' xs) "[>% [Hl' [Hstack HP]]]".
          injection H1; intros; subst.
          wp_load.
          iDestruct (is_stack_disj with "[Hstack]") as "[Hstack H]"; auto.
          iDestruct "H" as "[% | H]".
          ** subst.
             iDestruct (is_stack_empty with "Hstack") as "%".
             subst.
             iMod ("Hfail" with "HP") as "[HQ' HP]".
             iMod ("Hclose" with "[Hl' Hstack HP]").
             { iExists l'', (InjLV #()), []; iSplit; iFrame; auto. }
             iModIntro.
             wp_match.
             iRight; auto.
          ** iDestruct "H" as (h t) "%".
             subst.
             iMod ("Hclose" with "[Hl' Hstack HP]").
             { iExists l'', (InjRV (h, t)), xs; iSplit; iFrame; auto. }
             iModIntro.

             assert (to_val (h, t)%V = Some (h, t)%V) by apply to_of_val.
             assert (is_Some (to_val (h, t)%V)) by (exists (h, t)%V; auto).
             wp_match.
             unfold subst; simpl; fold of_val.

             wp_proj.
             wp_bind (CAS _ _ _).
             iInv N as "Hstack" "Hclose".
             iDestruct "Hstack" as (l''' v''' ys) "[>% [Hl''' [Hstack HP]]]".
             injection H4; intros; subst.
             assert (Decision (v''' = InjRV (h, t)%V)) as Heq by apply val_eq_dec.
             destruct Heq.
             ++ wp_cas_suc.
                subst.
                iDestruct (is_stack_cons with "Hstack") as "[Hstack H]".
                iDestruct "H" as (ys') "%"; subst.
                iDestruct "Hstack" as (t') "[% Hstack]".
                injection H5; intros; subst.
                iDestruct ("Hsucc" with "[HP]") as "> [HQ HP]"; auto.
                iMod ("Hclose" with "[Hl''' Hstack HP]").
                { iExists l''', t', ys'; iSplit; iFrame; auto. }
                iModIntro.
                wp_if.
                wp_proj.
                iLeft; iExists h; auto.
             ++ wp_cas_fail.
                iMod ("Hclose" with "[Hl''' Hstack HP]").
                { iExists l''', v''', ys; iSplit; iFrame; auto. }
                iModIntro.
                wp_if.
                iApply ("IH" with "Hsucc Hfail").
    - iIntros (v) "!# Hpush".
      iLöb as "IH".
      wp_rec.
      wp_rec.
      wp_lam.
      wp_alloc s as "Hs".
      wp_let.
      wp_bind (_ <- _)%E.
      iInv N' as "Hmail" "Hclose".
      iDestruct "Hmail" as (m') "[>% Hmail]".
      injection H; intros; subst.
      assert (exists n : namespace, hidden_eq n (nroot .@ "N''")) as foo
          by (exists (nroot .@ "N''"); unfold hidden_eq; auto).
      destruct foo as (N'', N''eq).
      assert (N ⊥ N'').
      { unfold hidden_eq in *; subst. apply ndot_ne_disjoint.
        intro. discriminate. }
      iMod (own_alloc (Excl ())) as (γ) "Hγ". done.
      iMod (inv_alloc N'' _ (stages γ P Q'' s v) with "[Hs Hpush]") as "#Istages".
      { iLeft; iFrame; auto. }
      iDestruct "Hmail" as "[H | H]".
      * wp_store.
        iMod ("Hclose" with "[H]").
        { iExists m'. iSplit; auto; iRight; iExists (v, #s)%V, γ.
          iFrame. iExists v, s; iSplit; auto. }
        iModIntro.
        wp_let.
        wp_lam.
        wp_proj.
        wp_bind (CAS _ _ _).
        iInv N'' as "Hstages" "Hclose".
        iDestruct "Hstages" as "[H | [H | [H | H]]]".
        + iDestruct "H" as "[Hs Hpush]".
          wp_cas_suc.
          iMod ("Hclose" with "[Hs Hγ]").
          { iRight; iRight; iRight; iFrame. }
          iModIntro.
          wp_if.
          wp_proj.

          assert (to_val v = Some v) by apply to_of_val.
          assert (is_Some (to_val v)) by (exists v; auto).
          wp_match.
          unfold subst; simpl; fold of_val.

          wp_bind (! _)%E.
          iInv N as "Hstack" "Hclose".
          iDestruct "Hstack" as (l' v' ys) "[>% [Hl' [Hstack HP]]]".
          injection H3; intros; subst.
          wp_load.
          iMod ("Hclose" with "[Hl' Hstack HP]").
          { iExists l', v', ys; iSplit; iFrame; auto. }
          iModIntro.
          wp_let.
          wp_let.
          wp_bind (CAS _ _ _).
          iInv N as "Hstack" "Hclose".
          iDestruct "Hstack" as (l'' v'' xs) "[>% [Hl'' [Hstack HP]]]".
          injection H4; intros; subst.
          assert (Decision (v' = v''%V)) as Heq by apply val_eq_dec.
          destruct Heq.
          ++ wp_cas_suc.
             iDestruct ("Hpush" with "[HP]") as "> [HP HQ]"; auto.
             iMod ("Hclose" with "[Hl'' Hstack HP]").
             { iExists l'', (InjRV (v, v')), (v :: xs); iSplit; iFrame; auto.
               iExists v'; iSplit; subst; auto. }
             iModIntro.
             wp_if.
             done.
          ++ wp_cas_fail.
             iMod ("Hclose" with "[Hl'' Hstack HP]").
             { iExists l'', v'', xs; iSplit; iFrame; auto. }
             iModIntro.
             wp_if.
             iApply ("IH" with "Hpush").
        + iDestruct "H" as "[Hs HQ'']".
          wp_cas_fail.
          iMod ("Hclose" with "[Hs Hγ]").
          { iRight; iRight; iLeft. iFrame. }
          iModIntro.
          wp_if.
          wp_match.
          done.
        + iDestruct "H" as "[Hs Hγ']".
          wp_cas_fail.
          by iDestruct (own_valid_2 with "Hγ Hγ'") as %?.
        + iDestruct "H" as "[Hs Hγ']".
          wp_cas_fail.
          by iDestruct (own_valid_2 with "Hγ Hγ'") as %?.
    * iDestruct "H" as (v' γ') "[Hm Hoffer]".
      wp_store.
      iMod ("Hclose" with "[Hm]").
      { iExists m'. iSplit; auto; iRight; iExists (v, #s)%V, γ.
        iFrame. iExists v, s; iSplit; auto. }
      iModIntro.
      wp_let.
      wp_lam.
      wp_proj.
      wp_bind (CAS _ _ _).
      iInv N'' as "Hstages" "Hclose".
      iDestruct "Hstages" as "[H | [H | [H | H]]]".
      + iDestruct "H" as "[Hs Hpush]".
        wp_cas_suc.
        iMod ("Hclose" with "[Hs Hγ]").
        { iRight; iRight; iRight; iFrame. }
        iModIntro.
        wp_if.
        wp_proj.

        assert (to_val v = Some v) by apply to_of_val.
        assert (is_Some (to_val v)) by (exists v; auto).
        wp_match.
        unfold subst; simpl; fold of_val.

        wp_bind (! _)%E.
        iInv N as "Hstack" "Hclose".
        iDestruct "Hstack" as (l' v'' ys) "[>% [Hl' [Hstack HP]]]".
        injection H3; intros; subst.
        wp_load.
        iMod ("Hclose" with "[Hl' Hstack HP]").
        { iExists l', v'', ys; iSplit; iFrame; auto. }
        iModIntro.
        wp_let.
        wp_let.
        wp_bind (CAS _ _ _).
        iInv N as "Hstack" "Hclose".
        iDestruct "Hstack" as (l'' v''' xs) "[>% [Hl'' [Hstack HP]]]".
        injection H4; intros; subst.
        assert (Decision (v'' = v'''%V)) as Heq by apply val_eq_dec.
        destruct Heq.
        ++ wp_cas_suc.
           iDestruct ("Hpush" with "[HP]") as "> [HP HQ]"; auto.
           iMod ("Hclose" with "[Hl'' Hstack HP]").
           { iExists l'', (InjRV (v, v'')), (v :: xs); iSplit; iFrame; auto.
             iExists v''; iSplit; subst; auto. }
           iModIntro.
           wp_if.
           done.
        ++ wp_cas_fail.
           iMod ("Hclose" with "[Hl'' Hstack HP]").
           { iExists l'', v''', xs; iSplit; iFrame; auto. }
           iModIntro.
           wp_if.
           iApply ("IH" with "Hpush").
      + iDestruct "H" as "[Hs HQ'']".
        wp_cas_fail.
        iMod ("Hclose" with "[Hs Hγ]").
        { iRight; iRight; iLeft. iFrame. }
        iModIntro.
        wp_if.
        wp_match.
        done.
      + iDestruct "H" as "[Hs Hγ']".
        wp_cas_fail.
        by iDestruct (own_valid_2 with "Hγ Hγ'") as %?.
      + iDestruct "H" as "[Hs Hγ']".
        wp_cas_fail.
        by iDestruct (own_valid_2 with "Hγ Hγ'") as %?.
  Qed.
End stack_works.
