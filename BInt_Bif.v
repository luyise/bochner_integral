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

Section BInt_def.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Definition BInt (bf : Bif E μ) :=
        lim_seq (fun n => BInt_sf μ (seq bf n)).

    Theorem is_lim_seq_BInt (bf : Bif E μ) :
        is_lim_seq (fun n => BInt_sf μ (seq bf n)) (BInt bf).
    Proof.
        case: bf => f s ι isf Hspw Hsl1.
        apply NM_Cauchy_seq_lim_seq_correct.
        apply Cauchy_seq_approx with f => //.
    Qed.

End BInt_def.

Notation "'∫B' bf" := (BInt bf)
        (only printing, at level 45, format "'[ ' '∫B'  bf ']'") : Bif_scope.

Section BInt_prop.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope Bif_scope.

    Lemma BInt_ext :
        ∀ bf bf' : Bif E μ, (∀ x : X, bf x = bf' x) ->
            BInt bf = BInt bf'.
    Proof.
        move => bf bf' Ext;
            case_eq bf => f s ι ints Hspw Hsl1 Eqπ;
            case_eq bf' => f' s' ι' ints' Hs'pw Hs'l1 Eqπ';
            unfold BInt => /=.
            rewrite Eqπ in Ext; simpl in Ext.
            rewrite Eqπ' in Ext; simpl in Ext.
        pose I := lim_seq (λ n : nat, BInt_sf μ (s n));
        pose I' := lim_seq (λ n : nat, BInt_sf μ (s' n)).
        pose HI := is_lim_seq_BInt bf;
            rewrite Eqπ in HI; simpl in HI;
            clearbody HI; fold I in HI.
        pose HI' := is_lim_seq_BInt bf';
            rewrite Eqπ' in HI'; simpl in HI';
            clearbody HI'; fold I' in HI'.
        move: HI' => /lim_seq_opp => HI'.
        assert (is_lim_seq (λ n : nat, BInt_sf μ (s n) + opp (BInt_sf μ (s' n)))%hy (I + opp I')%hy) as limdif
            by apply: lim_seq_plus => //.
        clear HI HI'.
        move: limdif => /(lim_seq_ext _ (λ n : nat, BInt_sf μ (s n - s' n)%sf) _ _) => limdif.
        assert (∀ n : nat, (BInt_sf μ (s n) + opp (BInt_sf μ (s' n)))%hy = BInt_sf μ (s n - s' n)%sf).
            move => n; rewrite BInt_sf_plus_aux.
            rewrite BInt_sf_scal_aux.
            rewrite scal_opp_one => //.
            apply ints.
            apply integrable_sf_scal, ints'.
        pose limdif' := limdif H; clearbody limdif';
            clear H; clear limdif.
        assert (is_lim_seq (λ n : nat, BInt_sf μ (s n - s' n)%sf) (I + opp I')%hy)
            as limdif by unfold is_lim_seq => //; clear limdif'.
        fold I I'.

        suff: (is_lim_seq (λ n : nat, BInt_sf μ (s n - s' n)%sf) zero).
        move => limdif'.
        assert (I + opp I' = zero)%hy.
        apply NM_is_lim_seq_unique with (λ n : nat, BInt_sf μ (s n - s' n)%sf) => //.
        apply (plus_reg_r (opp I'));
            rewrite H;
            rewrite plus_opp_r => //.
        clear I I' limdif.

        apply lim_seq_norm_zero.
        suff: (Lim_seq.is_lim_seq (‖(λ n : nat, BInt_sf μ (s n - s' n)%sf)‖)%fn 0%R).
            unfold Lim_seq.is_lim_seq;
            unfold Rbar_locally.
            unfold is_lim_seq => //.
        suff: (is_LimSup_seq' (‖ λ n : nat, BInt_sf μ (s n - s' n)%sf ‖)%fn 0).
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
        apply RIneq.Rle_lt_trans with (BInt_sf μ (‖(s n) - (s' n)‖)%sf).
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
            rewrite (LInt_p_ext _ _ (λ x : X, (‖ f' + (- s' n)%sf ‖)%fn x)).
            apply Hs'N'; apply Max.max_lub_r with N => //.
            move => x; unfold fun_norm, fun_plus.
            rewrite Ext => //.
            simpl; rewrite Rlimit.eps2 => //.
        all : swap 1 3.
        pose Lint_p_Bint_sf :=
            @Finite_BInt_sf_LInt_SFp _ _ μ (‖ s n - s' n ‖)%sf.
            rewrite <-LInt_p_SFp_eq in Lint_p_Bint_sf.
            2 : exact ι.
            2 : unfold sum_Rbar_nonneg.non_neg => x.
            2 : simpl; rewrite fun_sf_norm.
            2 : apply norm_ge_0.
            rewrite <-Lint_p_Bint_sf => //.
        
        all : swap 1 2.
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

        all : swap 1 2.
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

        1, 2 : apply integrable_sf_norm, integrable_sf_plus.
        2, 4 : apply integrable_sf_scal.
        1, 4 : apply ints.
        1, 2 : apply ints'.
    Qed.

    Lemma BInt_BInt_sf {s : simpl_fun E gen} : 
        ∀ π : integrable_sf μ s, ∀ ι : inhabited X,
        BInt_sf μ s = BInt (Bif_integrable_sf ι π).
    Proof.
        move => π ι; unfold BInt; simpl.
        symmetry; apply: lim_seq_eq.
        apply lim_seq_cte.
    Qed.

End BInt_prop.

Section BInt_indic.

    (* espace de départ *)
    Context {X : Set}.
    Context (ι : inhabited X).
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma BInt_indic :
        ∀ P : X -> Prop, ∀ π : measurable gen P, ∀ π' : is_finite (μ P),
            BInt (Bif_integrable_sf ι (integrable_sf_indic π π')) = μ P.
    Proof.
        move => P π π'.
        rewrite <-BInt_BInt_sf.
        apply BInt_sf_indic.
    Qed.

End BInt_indic.

Section BInt_op.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope hy_scope.
    Open Scope Bif_scope.

    Lemma BInt_plus :
        ∀ (bf : Bif E μ) (bg : Bif E μ),
            BInt (Bif_plus bf bg) = ((BInt bf) + (BInt bg))%hy.
    Proof.
        move => bf bg;
        case_eq bf => f sf ι isf Hfpw Hfl1 eqbf;
        case_eq bg => g sg ι' isg Hgpw Hgl1 eqbg;
        rewrite <-eqbf, <-eqbg. 
        unfold BInt.
        apply lim_seq_eq.
        apply (lim_seq_ext (fun n : nat => BInt_sf μ (sf n) + BInt_sf μ (sg n))%hy).
            move => n.
            rewrite eqbf eqbg => /=.
            rewrite BInt_sf_plus_aux => //.
            apply: lim_seq_plus.
            pose H := is_lim_seq_BInt (mk_Bif f sf ι isf Hfpw Hfl1);
                clearbody H; simpl in H; rewrite <-eqbf in H.
            assumption.
            pose H := is_lim_seq_BInt (mk_Bif g sg ι' isg Hgpw Hgl1);
                clearbody H; simpl in H; rewrite <-eqbg in H.
            assumption.
    Qed.

    Lemma BInt_scal :
        ∀ (bf : Bif E μ), ∀ (a : R_AbsRing),
            BInt (Bif_scal a bf) = (a ⋅ (BInt bf))%hy.
    Proof.
        move => bf a.
        case: bf => f sf ι isf Hfpw Hfl1.
        apply lim_seq_eq.
        apply (lim_seq_ext (fun n : nat => a ⋅ (BInt_sf μ (sf n)))%hy).
            move => n; rewrite BInt_sf_scal_aux => //.
            apply: lim_seq_scal_r.
            pose H := is_lim_seq_BInt (mk_Bif f sf ι isf Hfpw Hfl1);
                clearbody H; simpl in H.
            assumption.
    Qed.

    Lemma norm_BInt_le :
        ∀ (bf : Bif E μ),
            ‖ BInt bf ‖%hy <= BInt (‖bf‖)%Bif.
    Proof.
        move => bf.
        case: bf => f sf ι isf Hfpw Hfl1.
        suff: (Rbar_le (‖ lim_seq (λ n : nat, BInt_sf μ (sf n)) ‖)%hy (lim_seq (λ n : nat, BInt_sf μ (‖ sf n ‖)%sf)))
            by simpl => //.
        apply is_lim_seq_le with (λ n : nat, ‖ BInt_sf μ (sf n) ‖)%hy (λ n : nat, BInt_sf μ (‖ sf n ‖%sf)).
            move => n; apply norm_Bint_sf_le.
            apply lim_seq_norm.
            pose H := is_lim_seq_BInt (mk_Bif f sf ι isf Hfpw Hfl1);
                clearbody H; simpl in H.
            assumption.
            pose H := is_lim_seq_BInt (Bif_norm (mk_Bif f sf ι isf Hfpw Hfl1));
                clearbody H; simpl in H.
            assumption.
    Qed.

End BInt_op.

Section BInt_linearity.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope hy_scope.
    Open Scope Bif_scope.
    
    Lemma BInt_linearity :
        ∀ (bf : Bif E μ) (bg : Bif E μ), ∀ a b : R,
            BInt (a ⋅ bf + b ⋅ bg)
            = (a ⋅ (BInt bf) + (b ⋅ (BInt bg)))%hy.
    Proof.
        move => bf bg a b.
        rewrite BInt_plus.
        do 2 rewrite BInt_scal => //.
    Qed.

    Lemma BInt_zero :
        ∀ (bf : Bif E μ),
            (∀ x : X, bf x = zero) -> BInt bf = zero.
    Proof.
        move => bf Hbf.
        rewrite (BInt_ext bf (Bif_zero (ax_notempty bf))).
        unfold Bif_zero. 
        rewrite <-BInt_BInt_sf.
        unfold BInt_sf => /=.
        rewrite sum_O.
        rewrite scal_zero_r => //.
        move => x; rewrite Hbf.
        rewrite Bif_zero_fun => //.
    Qed.

    Lemma BInt_minus :
        ∀ bf bg : Bif E μ,
            BInt (bf - bg)%Bif = ((BInt bf) - (BInt bg))%hy.
    Proof.
        move => bf bg.
        rewrite BInt_plus BInt_scal.
        rewrite scal_opp_one => //.
    Qed.

    Lemma BInt_opp :
        ∀ bf : Bif E μ,
            (BInt (- bf)) = (- (BInt bf))%hy.
    Proof.
        move => bf.
        rewrite BInt_scal scal_opp_one => //.
    Qed.

End BInt_linearity.