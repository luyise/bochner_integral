Add LoadPath "~/Documents/CoqGit/completeModuleSummation" as CMS.

From Coq Require Import 
    ssreflect
    ssrsearch
    Utf8

    Rdefinitions
    Rbasic_fun
.

From Coquelicot Require Import
    Hierarchy
    Rbar
    Lim_seq
.
    
Require Import
    hierarchy_notations
    simpl_fun
    BInt_sf
    Bsf_Lsf
    CUS_Lim_seq
    Bi_fun
.

From CMS Require Import
    series
.

Require Import
    measure
    LInt_p
    Rbar_compl
    simple_fun
    measurable_fun
    sigma_algebra
.

Section BInt_Bif_def.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.
    Context {f : X -> E}.

    Definition BInt_Bif (π : Bif μ f) :=
        match π return E with (approximation s _ _ _) =>
            lim_seq (fun n => BInt_sf (s n))
        end.

    Theorem is_lim_seq_BInt_Bif (bf : Bif μ f) :
        match bf return Prop with (approximation s _ _ _) =>
            is_lim_seq (fun n => BInt_sf (s n)) (BInt_Bif bf)
        end.
    Proof.
        case: bf => s ι Hspw Hsl1.
        apply NM_Cauchy_seq_lim_seq_correct.
        apply Cauchy_seq_approx with f => //.
    Qed.

End BInt_Bif_def.

Notation "'∫B' bf" := (BInt_Bif bf)
        (only printing, at level 45, format "'[ ' '∫B'  bf ']'") : Bif_scope.

Section BInt_Bif_prop.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope Bif_scope.

    Lemma BInt_Bif_ext :
        ∀ f : X -> E, ∀ bf bf' : Bif μ f,
            BInt_Bif bf = BInt_Bif bf'.
    Proof.
        move => f bf bf';
            case_eq bf => s ι Hspw Hsl1 Eqπ;
            case_eq bf' => s' ι' Hs'pw Hs'l1 Eqπ';
            unfold BInt_Bif.
        pose I := lim_seq (λ n : nat, BInt_sf (s n));
        pose I' := lim_seq (λ n : nat, BInt_sf (s' n)).
        pose HI := is_lim_seq_BInt_Bif bf;
            rewrite Eqπ in HI; simpl in HI;
            clearbody HI; fold I in HI.
        pose HI' := is_lim_seq_BInt_Bif bf';
            rewrite Eqπ' in HI'; simpl in HI';
            clearbody HI'; fold I' in HI'.
        move: HI' => /lim_seq_opp => HI'.
        assert (is_lim_seq (λ n : nat, BInt_sf (s n) + opp (BInt_sf (s' n)))%hy (I + opp I')%hy) as limdif
            by apply: lim_seq_plus => //.
        clear HI HI'.
        move: limdif => /(lim_seq_ext _ (λ n : nat, BInt_sf (s n - s' n)%sf) _ _) => limdif.
        assert (∀ n : nat, (BInt_sf (s n) + opp (BInt_sf (s' n)))%hy = BInt_sf (s n - s' n)%sf).
            move => n; rewrite BInt_sf_plus_aux.
            rewrite BInt_sf_scal_aux.
            rewrite scal_opp_one => //.
        pose limdif' := limdif H; clearbody limdif';
            clear H; clear limdif.
        assert (is_lim_seq (λ n : nat, BInt_sf (s n - s' n)%sf) (I + opp I')%hy)
            as limdif by unfold is_lim_seq => //; clear limdif'.
        fold I I'.

        suff: (is_lim_seq (λ n : nat, BInt_sf (s n - s' n)%sf) zero).
        move => limdif'.
        assert (I + opp I' = zero)%hy.
        apply NM_is_lim_seq_unique with (λ n : nat, BInt_sf (s n - s' n)%sf) => //.
        apply (plus_reg_r (opp I'));
            rewrite H;
            rewrite plus_opp_r => //.
        clear I I' limdif.

        apply lim_seq_norm_zero.
        suff: (Lim_seq.is_lim_seq (‖(λ n : nat, BInt_sf (s n - s' n)%sf)‖)%fn 0%R).
            unfold Lim_seq.is_lim_seq;
            unfold Rbar_locally.
            unfold is_lim_seq => //.
        suff: (is_LimSup_seq' (‖ λ n : nat, BInt_sf (s n - s' n)%sf ‖)%fn 0).
            move => HLS.
            simpl in HLS.
            apply is_lim_seq_spec; unfold is_lim_seq'.
            move => sigɛ.
            case: (HLS sigɛ) => _ {}HLS;
                case: HLS => N HLS.
            exists N => n Hn.
            pose HLSn := (HLS n Hn);
                clearbody HLSn;
                clear HLS Hn.
                unfold Rminus; rewrite RIneq.Ropp_0.
                rewrite Raxioms.Rplus_0_l in HLSn.
                rewrite (proj1 (RIneq.Rplus_ne _)).
                rewrite Rabs_pos_eq => //.
                unfold fun_norm; apply norm_ge_0.
        
        unfold fun_norm.

        unfold is_LimSup_seq' => ɛ; split; swap 1 2.
        simpl; rewrite Raxioms.Rplus_0_l.

        2 : move => N0.
        2 : exists N0; split => //.
        2 : simpl; unfold Rminus; rewrite Raxioms.Rplus_0_l.
        2 : apply RIneq.Rlt_le_trans with 0.
        2 : case: ɛ => ɛ Hɛ => /=.
        2 : apply RIneq.Ropp_lt_gt_0_contravar => //.
        2 : apply norm_ge_0.

        case: ɛ => ɛ Hɛ.

        pose sighalfɛ := RIneq.mkposreal (ɛ * /2) (R_compl.Rmult_lt_pos_pos_pos _ _ (RIneq.Rgt_lt _ _ Hɛ) RIneq.pos_half_prf).
        case: (Hsl1 sighalfɛ) => [HsMaj {}Hs].
        case: (Hs'l1 sighalfɛ) => [Hs'Maj {}Hs'].
        case: Hs => N HsN.
        case: Hs' => N' Hs'N'.
        exists (max N N').
        move => n Hn => /=.
        unfold minus.
        apply RIneq.Rle_lt_trans with (BInt_sf (‖(s n) - (s' n)‖)%sf).
            apply norm_Bint_sf_le.
        rewrite (BInt_sf_LInt_SFp).
        rewrite <-LInt_p_SFp_eq.
            2 : exact ι.
            all : swap 1 2.
            unfold sum_Rbar_nonneg.non_neg => x /=.
            rewrite fun_sf_norm.
            apply norm_ge_0.
        assert (∀ x : X, Rbar_le ((‖ s n + (- s' n)%sf ‖)%fn x) (((‖ f - s n ‖) + (‖ f - s' n ‖))%fn x)).
            move => x; simpl.
            unfold fun_norm, fun_plus.
            do 2 rewrite fun_sf_scal.
            replace (s n x) with ((s n x) + zero)%hy at 1.
                2 : rewrite plus_zero_r => //.
            replace zero with (opp (f x) + f x)%hy at 1.
                2 : apply plus_opp_l.
            rewrite plus_assoc.
            setoid_rewrite plus_comm at 3.
            setoid_rewrite <-norm_opp at 2.
            rewrite opp_plus; setoid_rewrite scal_opp_one at 2.
            rewrite opp_opp; rewrite <-plus_assoc.
            apply norm_triangle.

        pose Ineq := (LInt_p_monotone μ (‖ s n - s' n ‖)%fn ((‖ f - s n ‖) + (‖ f - s' n ‖))%fn H);
            clearbody Ineq.
        replace ɛ with (real ɛ).
            2 : easy.
        rewrite <-Rbar_lt_finite_eq_rlt.
            3 : easy.
        rewrite (LInt_p_ext _ _ (λ x : X, (‖ s n + (- s' n)%sf ‖)%fn x)).
            2 : unfold fun_norm.
            2 : setoid_rewrite fun_sf_norm.
            2 : setoid_rewrite fun_sf_plus => //.
        apply (Rbar_le_lt_trans _ _ (Finite ɛ) Ineq).
        unfold fun_plus at 1.
        rewrite (LInt_p_ext _ _ (λ x : X, Rbar_plus ((‖ f + (- s n)%sf ‖)%fn x) ((‖ f + (- s' n)%sf ‖)%fn x)%hy)).
            2 : by [].
        rewrite LInt_p_plus.
            2 : exact ι.
            2, 4 : unfold sum_Rbar_nonneg.non_neg => x.
            2, 3 : unfold fun_norm; apply norm_ge_0.
        replace ɛ with (real (Rbar_plus (ɛ*/2) (ɛ*/2))).
        clear H Ineq.
        unfold "_ - _" in HsN.
        simpl in HsN, Hs'N'.
        rewrite Raxioms.Rplus_0_l in Hs'N'.
        rewrite Raxioms.Rplus_0_l in HsN.
        apply (Rbar_plus_lt_compat (LInt_p μ (λ x : X, (‖ f + (- s n)%sf ‖)%fn x)) (ɛ*/2) 
                                    (LInt_p μ (λ x : X, (‖ f + (- s' n)%sf ‖)%fn x)) (ɛ*/2)).
            apply HsN; apply Max.max_lub_l with N' => //.
            apply Hs'N'; apply Max.max_lub_r with N => //.
            simpl; rewrite Rlimit.eps2 => //.
        all : swap 1 3.
        pose Lint_p_Bint_sf :=
            Finite_BInt_sf_LInt_SFp (‖ s n - s' n ‖)%sf.
            rewrite <-LInt_p_SFp_eq in Lint_p_Bint_sf.
            2 : exact ι.
            2 : unfold sum_Rbar_nonneg.non_neg => x.
            2 : simpl; rewrite fun_sf_norm.
            2 : apply norm_ge_0.
            rewrite <-Lint_p_Bint_sf => //.

        assert
            (∀ x : X, is_lim_seq (fun k => (‖ s k + (- s' n)%sf ‖)%fn x) ((‖ f + (- s' n)%sf ‖)%fn x)) as Limseqnorm.
            move => x; unfold fun_norm.
            apply lim_seq_norm.
            apply lim_seq_plus.
            apply Hspw.
            apply lim_seq_cte.
        apply measurable_fun_ext with (fun x : X => (Lim_seq' (λ k : nat, (‖ s k + (- s' n)%sf ‖)%fn x))).
            move => x; rewrite <-Lim_seq_seq'.
            apply is_lim_seq_unique.
            unfold Lim_seq.is_lim_seq.
            unfold Rbar_locally => /=.
            apply: Limseqnorm.
        apply measurable_fun_Lim_seq'.
        move => k; unfold sum_Rbar_nonneg.non_neg => x; apply norm_ge_0.
        move => k; apply measurable_fun_R_Rbar.
        
        apply: (measurable_fun_composition _ open).
        apply measurable_fun_ext with ((s k + (- s' n)%sf))%sf.
            move => x.
            rewrite fun_sf_plus => //.
        apply (measurable_fun_sf (s k - s' n)%sf).
        move => P; move /sigma_algebra_R_Rbar_new.measurable_R_equiv_oo.
        apply measurable_fun_continuous.
        apply filterlim_norm.

        assert
            (∀ x : X, is_lim_seq (fun k => (‖ s k + (- s n)%sf ‖)%fn x) ((‖ f + (- s n)%sf ‖)%fn x)) as Limseqnorm.
            move => x; unfold fun_norm.
            apply lim_seq_norm.
            apply lim_seq_plus.
            apply Hspw.
            apply lim_seq_cte.
        apply measurable_fun_ext with (fun x : X => (Lim_seq' (λ k : nat, (‖ s k + (- s n)%sf ‖)%fn x))).
            move => x; rewrite <-Lim_seq_seq'.
            apply is_lim_seq_unique.
            unfold Lim_seq.is_lim_seq.
            unfold Rbar_locally => /=.
            apply: Limseqnorm.
        apply measurable_fun_Lim_seq'.
        move => k; unfold sum_Rbar_nonneg.non_neg => x; apply norm_ge_0.
        move => k; apply measurable_fun_R_Rbar.
        
        apply: (measurable_fun_composition _ open).
        apply measurable_fun_ext with ((s k + (- s n)%sf))%sf.
            move => x.
            rewrite fun_sf_plus => //.
        apply (measurable_fun_sf (s k - s n)%sf).
        move => P; move /sigma_algebra_R_Rbar_new.measurable_R_equiv_oo.
        apply measurable_fun_continuous.
        apply filterlim_norm.
    Qed.

    Lemma BInt_Bif_BInt_sf : ∀ s : simpl_fun E μ, ∀ ι : inhabited X,
        BInt_sf s = BInt_Bif (Bif_sf ι s).
    Proof.
        move => s ι; unfold BInt_Bif; simpl.
        symmetry; apply: lim_seq_eq.
        apply lim_seq_cte.
    Qed.

End BInt_Bif_prop.

Section BInt_Bif_indic.

    (* espace de départ *)
    Context {X : Set}.
    Context (ι : inhabited X).
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma BInt_Bif_indic :
        ∀ P : X -> Prop, ∀ π : measurable gen P, ∀ π' : is_finite (μ P),
            BInt_Bif (Bif_sf ι (sf_indic_aux μ P π π')) = μ P.
    Proof.
        move => P π π'.
        rewrite <-BInt_Bif_BInt_sf.
        apply BInt_sf_indic.
    Qed.

End BInt_Bif_indic.

Section BInt_Bif_op.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.
    Context {f g : X -> E}.

    Open Scope hy_scope.
    Open Scope Bif_scope.

    Lemma BInt_Bif_plus :
        ∀ (bf : Bif μ f) (bg : Bif μ g),
            BInt_Bif (Bif_plus bf bg) = ((BInt_Bif bf) + (BInt_Bif bg))%hy.
    Proof.
        move => bf bg;
        case: bf => sf ι Hfpw Hfl1;
        case: bg => sg ι' Hgpw Hgl1.
        unfold BInt_Bif, Bif_plus.
        apply lim_seq_eq.
        apply (lim_seq_ext (fun n : nat => BInt_sf (sf n) + BInt_sf (sg n))%hy).
            move => n; rewrite BInt_sf_plus_aux => //.
            apply: lim_seq_plus.
            pose H := is_lim_seq_BInt_Bif (approximation f sf ι Hfpw Hfl1);
                clearbody H; simpl in H.
            assumption.
            pose H := is_lim_seq_BInt_Bif (approximation g sg ι' Hgpw Hgl1);
                clearbody H; simpl in H.
            assumption.
    Qed.

    Lemma BInt_Bif_scal :
        ∀ (bf : Bif μ f), ∀ (a : R_AbsRing),
            BInt_Bif (Bif_scal a bf) = (a ⋅ (BInt_Bif bf))%hy.
    Proof.
        move => bf a.
        case: bf => sf ι Hfpw Hfl1.
        unfold BInt_Bif, Bif_scal.
        apply lim_seq_eq.
        apply (lim_seq_ext (fun n : nat => a ⋅ (BInt_sf (sf n)))%hy).
            move => n; rewrite BInt_sf_scal_aux => //.
            apply: lim_seq_scal_r.
            pose H := is_lim_seq_BInt_Bif (approximation f sf ι Hfpw Hfl1);
                clearbody H; simpl in H.
            assumption.
    Qed.

    Lemma norm_BInt_Bif_le :
        ∀ (bf : Bif μ f),
            ‖ BInt_Bif bf ‖%hy <= BInt_Bif (‖bf‖)%Bif.
    Proof.
        move => bf.
        case: bf => sf ι Hfpw Hfl1.
        unfold BInt_Bif, Bif_norm.
        suff: (Rbar_le (‖ lim_seq (λ n : nat, BInt_sf (sf n)) ‖)%hy (lim_seq (λ n : nat, BInt_sf (‖ sf n ‖)%sf)))
            by simpl => //.
        apply is_lim_seq_le with (λ n : nat, ‖ BInt_sf (sf n) ‖)%hy (λ n : nat, BInt_sf (‖ sf n ‖%sf)).
            move => n; apply norm_Bint_sf_le.
            apply lim_seq_norm.
            pose H := is_lim_seq_BInt_Bif (approximation f sf ι Hfpw Hfl1);
                clearbody H; simpl in H.
            assumption.
            pose H := is_lim_seq_BInt_Bif (Bif_norm (approximation f sf ι Hfpw Hfl1));
                clearbody H; simpl in H.
            assumption.
    Qed.

End BInt_Bif_op.

Section BInt_Bif_linearity.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.
    Context {f g : X -> E}.

    Open Scope hy_scope.
    Open Scope Bif_scope.
    
    Lemma BInt_sf_linearity :
        ∀ (bf : Bif μ f) (bg : Bif μ g), ∀ a b : R,
            BInt_Bif (a ⋅ bf + b ⋅ bg)
            = (a ⋅ (BInt_Bif bf) + (b ⋅ (BInt_Bif bg)))%hy.
    Proof.
        move => bf bg a b.
        rewrite BInt_Bif_plus.
        do 2 rewrite BInt_Bif_scal => //.
    Qed.

End BInt_Bif_linearity.