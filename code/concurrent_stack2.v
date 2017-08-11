From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang proofmode notation.
From iris.algebra Require Import excl.
Set Default Proof Using "Type".

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
     | SOME "x" => take_offer "x"
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

  Definition stages γ (P : val → iProp Σ) l v :=
    ((l ↦ #0 ∗ P v)
     ∨ (l ↦ #1)
     ∨ (l ↦ #2 ∗ own γ (Excl ())))%I.

  Definition is_offer γ (P : val → iProp Σ) (v : val) : iProp Σ :=
    (∃ v' l, ⌜v = (v', #l)%V⌝ ∗ ∃ ι, inv ι (stages γ P l v'))%I.

  Definition mailbox_inv (P : val → iProp Σ) (v : val) : iProp Σ :=
    (∃ l, ⌜v = #l⌝ ∗ (l ↦ NONEV ∨ (∃ v' γ, l ↦ SOMEV v' ∗ is_offer γ P v')))%I.

  (* A partial specification for revoke that will be useful later *)
  Lemma revoke_works N γ P l v :
    inv N (stages γ P l v) ∗ own γ (Excl ()) -∗
    WP revoke_offer (v, #l)
      {{ v', (∃ v'' : val, ⌜v' = InjRV v''⌝ ∗ P v'') ∨ ⌜v' = InjLV #()⌝ }}.
  Proof.
    iIntros "[#Hinv Hγ]".
    wp_let.
    wp_proj.
    wp_bind (CAS _ _ _).
    iInv N as "Hstages" "Hclose".
    iDestruct "Hstages" as "[H | [H | H]]".
    - iDestruct "H" as "[Hl HP]".
      wp_cas_suc.
      iMod ("Hclose" with "[Hl Hγ]").
      iRight; iRight; iFrame.
      iModIntro.
      wp_if.
      wp_proj.
      iLeft.
      iExists v; iSplit; auto.
    - wp_cas_fail.
      iMod ("Hclose" with "[H]").
      iRight; iLeft; auto.
      iModIntro.
      wp_if.
      iRight; auto.
    - iDestruct "H" as "[Hl H]".
      wp_cas_fail.
        by iDestruct (own_valid_2 with "H Hγ") as %?.
  Qed.

  (* A partial specification for take that will be useful later *)
  Lemma take_works γ N P v l :
    inv N (stages γ P l v) -∗
    WP take_offer (v, LitV l)%V
      {{ v', (∃ v'' : val, ⌜v' = InjRV v''⌝ ∗ P v'') ∨ ⌜v' = InjLV #()⌝ }}.
  Proof.
    iIntros "#Hinv".
    wp_lam.
    wp_proj.
    wp_bind (CAS _ _ _).
    iInv N as "Hstages" "Hclose".
    iDestruct "Hstages" as "[H | [H | H]]".
    - iDestruct "H" as "[H HP]".
      wp_cas_suc.
      iMod ("Hclose" with "[H]").
      iRight; iLeft; done.
      iModIntro.
      wp_if.
      wp_proj.
      iLeft.
      auto.
    - wp_cas_fail.
      iMod ("Hclose" with "[H]").
      iRight; iLeft; done.
      iModIntro.
      wp_if.
      auto.
    - iDestruct "H" as "[Hl Hγ]".
      wp_cas_fail.
      iMod ("Hclose" with "[Hl Hγ]").
      iRight; iRight; iFrame.
      iModIntro.
      wp_if.
      auto.
  Qed.
End side_channel.

Section mailbox.
  Context `{!heapG Σ}.
  Implicit Types l : loc.

  Theorem mailbox_works {channelG0 : channelG Σ} (P : val → iProp Σ) (Φ : val → iProp Σ) :
    (∀ (v₁ v₂ : val),
      ⌜Closed [] v₁⌝
     ∗ ⌜Closed [] v₂⌝
     ∗ (∀ (v : val), □ (P v -∗ WP v₁ v {{v',
          (∃ v'', ⌜v' = SOMEV v''⌝ ∗ P v'') ∨ ⌜v' = NONEV⌝}}))
     ∗ (□ (WP v₂ #() {{v', (∃ v'', ⌜v' = SOMEV v''⌝ ∗ P v'') ∨ ⌜v' = NONEV⌝}}))
     -∗ Φ (v₁, v₂)%V)
    -∗ WP mailbox #() {{ Φ }}.
  Proof.
    iIntros "HΦ".
    pose proof (nroot .@ "N") as N.
    rewrite -wp_fupd.
    wp_lam.
    wp_alloc l as "Hl".
    wp_let.
    iMod (inv_alloc N _ (mailbox_inv P #l) with "[Hl]") as "#Hinv".
    iExists l; iSplit; try iLeft; auto.
    iModIntro.
    iApply "HΦ"; repeat iSplit; try (iPureIntro; apply _).
    * iIntros (v) "!# HP".
      wp_rec.
      wp_bind (mk_offer v).
      pose proof (nroot .@ "N'") as N'.
      rewrite -wp_fupd.
      wp_lam.
      iMod (own_alloc (Excl ())) as (γ) "Hγ". done.
      wp_alloc l' as "Hl'".
      iMod (inv_alloc N' _ (stages γ P l' v) with "[HP Hl']") as "#Hinv'".
      iLeft; iFrame.
      iModIntro.
      wp_let.
      wp_bind (#l <- _)%E.
      iInv N as "Hmailbox" "Hclose".
      iDestruct "Hmailbox" as (l'') "[>% H]".
      injection H; intros; subst.
      iDestruct "H" as "[H | H]";
        [idtac | iDestruct "H" as (v' γ') "[Hl H]"];
        wp_store;
        [iMod ("Hclose" with "[H]") | iMod ("Hclose" with "[Hl H]")];
        try  (iExists l''; iSplit; try iRight; auto;
              iExists (v, #l')%V, γ; iFrame;
              iExists v, l'; auto);
        iModIntro;
        wp_let;
        iApply (revoke_works with "[Hγ Hinv]"); auto.
    * iIntros "!#".
      wp_rec.
      wp_bind (! _)%E.
      iInv N as "Hmailbox" "Hclose".
      iDestruct "Hmailbox" as (l') "[>% H]".
      injection H; intros; subst.
      iDestruct "H" as "[H | H]".
      + wp_load.
        iMod ("Hclose" with "[H]").
        iExists l'; iSplit; auto.
        iModIntro.
        wp_let.
        wp_match.
        iRight; auto.
      + iDestruct "H" as (v' γ) "[Hl' #Hoffer]".
        wp_load.
        iMod ("Hclose" with "[Hl' Hoffer]").
        { iExists l'; iSplit; auto.
          iRight; iExists v', γ; by iSplit. }
        iModIntro.
        wp_let.
        wp_match.
        iDestruct "Hoffer" as (v'' l'') "[% Hoffer]".
        iDestruct "Hoffer" as (ι) "Hinv'".
        subst.
        iApply take_works; auto.
  Qed.
End mailbox.

Section stack_works.
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

  Theorem stack_works {channelG0 : channelG Σ} P Φ :
    (∀ (f₁ f₂ : val),
            (□ WP f₁ #() {{ v, (∃ (v' : val), v ≡ SOMEV v' ∗ P v')  ∨ v ≡ NONEV }})
         -∗ (∀ (v : val), □ (P v -∗ WP f₂ v {{ v, True }}))
         -∗ Φ (f₁, f₂)%V)%I
    -∗ WP mk_stack #()  {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp_lam.
    wp_bind (mailbox _).
    iApply (mailbox_works P).
    iIntros (put get) "[% [% [#Hput #Hget]]]".
    wp_let; wp_proj; wp_let; wp_proj; wp_let; wp_alloc l' as "Hl'".
    pose proof (nroot .@ "N") as N.
    iMod (inv_alloc N _ (stack_inv P #l') with "[Hl']") as "#Hisstack".
    { iExists l', NONEV; iFrame; iSplit; auto. iApply is_stack_unfold; iLeft; done. }
    wp_let.
    iApply "HΦ".
    (* The verification of pop *)
    - iIntros "!#".
      iLöb as "IH".
      wp_rec;  wp_bind (get _).
      (* Switch from proving WP put #() {{ P }} to
       * Q -∗ P where Q is the spec we have already assumed for P
       *)
      iApply wp_wand; auto.
      iIntros (v) "Hv".
      iDestruct "Hv" as "[H | H]".
      * iDestruct "H" as (v') "[% HP]".
        subst.
        (* This is just some technical fidgetting to get wp_match to behave.
         * It is safe to ignore
         *)
        assert (to_val v' = Some v') by apply to_of_val.
        assert (is_Some (to_val v')) by (exists v'; auto).
        assert (to_val (InjRV v') = Some (InjRV v')) by apply to_of_val.
        assert (is_Some (to_val (InjRV v'))) by (exists (InjRV v'); auto).
        wp_match.
        iLeft; iExists v'; auto.
      * iDestruct "H" as "%"; subst.
        wp_match; wp_bind (! #l')%E.
        iInv N as "Hstack" "Hclose".
        iDestruct "Hstack" as (l'' v'') "[>% [Hl' Hstack]]".
        injection H1; intros; subst.
        wp_load.
        iDestruct (is_stack_disj with "Hstack") as "[Hstack #Heq]".
        iMod ("Hclose" with "[Hl' Hstack]").
        { iExists l'', v''; iFrame; auto. }
        iModIntro.
        iDestruct "Heq" as "[H | H]".
        + iRewrite "H"; wp_match; iRight; auto.
        + iDestruct "H" as (h t) "H"; iRewrite "H".
          (* For technical reasons, wp_match gets confused by this
           * position. Hence the assertions. They can be safely ignored
           *)
          assert (to_val (h, t)%V = Some (h, t)%V) by apply to_of_val.
          assert (is_Some (to_val (h, t)%V)) by (exists (h, t)%V; auto).
          wp_match. fold of_val.
          (* Push the substitution through *)
          unfold subst; simpl; fold subst.
          (* Now remove the substitution entirely by observing that we're
           * substituting into a closed term
           *)
          assert (subst "hd" (h, t) get = get) as Hremovesubst.
          { apply (subst_is_closed [] get "hd" (h, t)); auto;
            intro. inversion H4. }
          unfold subst in Hremovesubst.
          rewrite Hremovesubst.
          (* Now back to our regularly scheduled verification *)
          wp_bind (CAS _ _ _); wp_proj.
          iInv N as "Hstack" "Hclose".
          iDestruct "Hstack" as (l''' v''') "[>% [Hl'' Hstack]]".
          injection H4; intros; subst.
          (* Case on whether or not the stack has been updated
           * TODO: I hate this "assert to destruct" pattern.
           * Can we consolidate?
           *)
          assert (Decision (v''' = InjRV (h, t)%V)) as Heq by apply val_eq_dec.
          destruct Heq.
          ++ (* If nothing has changed, the cas succeeds *)
            wp_cas_suc.
            iDestruct (is_stack_unfold with "Hstack") as "[Hstack | Hstack]".
            subst.
            iDestruct "Hstack" as "%"; discriminate.
            iDestruct "Hstack" as (h' t') "[% [HP Hstack]]".
            subst.
            injection H5.
            intros.
            subst.
            iMod ("Hclose" with "[Hl'' Hstack]").
            { iExists l''', t'; iFrame; auto. }
            iModIntro.
            wp_if; wp_proj; iLeft; auto.
          ++ (* The case in which we fail *)
            wp_cas_fail.
            iMod ("Hclose" with "[Hl'' Hstack]").
            iExists l''', v'''; iFrame; auto.
            iModIntro.
            wp_if.
            (* Now we use our IH to loop *)
            iApply "IH".
    (* The verification of push. This is actually markedly simpler. *)
    - iIntros (v) "!# HP".
      simpl in *.
      fold of_val in *.
      (* We grab an IH to be used in the case that we loop *)
      iLöb as "IH" forall (v).
      wp_rec.
      wp_bind (put _).
      (* Switch from proving WP put #() {{ P }} to
       * Q -∗ P where Q is the spec we have already assumed for put
       *)
      iApply (wp_wand with "[HP]").
      iApply "Hput"; auto.
      iIntros (v') "Hv'".
      iDestruct "Hv'" as "[H | H]".
      * iDestruct "H" as (v'') "[% HP]"; subst.
        (* Again we have that wp_match gets confused so we help it
         * out by adding some assumptions it needs explicitly
         *)
        assert (to_val v'' = Some v'') by apply to_of_val.
        assert (is_Some (to_val v'')) by (exists v''; auto).
        wp_match. fold of_val.
        (* Push the substitution through the term *)
        unfold subst; simpl.
        wp_bind (! _)%E.
        iInv N as "Hstack" "Hclose".
        iDestruct "Hstack" as (l'' v') "[>% [Hl' Hstack]]".
        injection H3; intros; subst.
        wp_load.
        iMod ("Hclose" with "[Hl' Hstack]").
        { by (iExists l'', v'; iFrame). }
        iModIntro.
        wp_let; wp_let; wp_bind (CAS _ _ _).
        iInv N as "Hstack" "Hclose".
        iDestruct "Hstack" as (l''' v''') "[>% [Hl'' Hstack]]".
        injection H4; intros; subst.
        (* Now we case to see if the stack is unchanged *)
        assert (Decision (v''' = v'%V)) as Heq by apply val_eq_dec.
        destruct Heq.
        + wp_cas_suc.
          iMod ("Hclose" with "[Hl'' HP Hstack]").
          { iExists l''', (InjRV (v'', v')%V).
            iSplit; iFrame; auto.
            iApply is_stack_unfold; iRight.
            iExists v'', v'; iFrame; iSplit; subst; auto. }
          iModIntro.
          wp_if.
          done.
        + wp_cas_fail.
          iMod ("Hclose" with "[Hl'' Hstack]").
          iExists l''', v'''; iFrame; auto.
          iModIntro.
          wp_if.
          iApply ("IH" with "HP").
      * (* This is the case that our sidechannel offer succeeded *)
        iDestruct "H" as "%"; subst.
        wp_match.
        done.
  Qed.
End stack_works.
