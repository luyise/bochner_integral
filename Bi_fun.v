
Add LoadPath "~/Documents/CoqGit/completeModuleSummation" as CMS.

From Coq Require Import 
    ssreflect
    ssrsearch
    Utf8
    Lia
    Lra

    Rdefinitions
    Rbasic_fun
    Raxioms
.

From Coquelicot Require Import
    Hierarchy
    Rbar
    Lim_seq
    Markov
.
    
Require Import
    hierarchy_notations
    simpl_fun
    BInt_sf
    Bsf_Lsf
    CUS_Lim_seq
    topology_compl
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

Lemma is_LimSup_seq'_scal_l :
  forall u : nat -> Rbar, forall a : R, 0%R <= a -> forall l : R, is_LimSup_seq' u l ->
    is_LimSup_seq' (fun n => Rbar_mult a (u n)) (Rbar_mult a l).
Proof.
    move => u a Ha l Hl;
        unfold is_LimSup_seq' in Hl.
        (*case: (Hl RIneq.posreal_one) => Hl11 Hl12.
        case: Hl12 => N' HN'.
        simpl in Hl11, HN'.*)
      
    unfold is_LimSup_seq' => /=; move => [ɛ Hɛ]; split.
    case: (RIneq.Req_EM_T a 0).
        move => -> /= N; exists N; split.
        apply Nat.le_refl.
        rewrite Rbar_mult_0_l.
        rewrite RIneq.Rmult_0_l.
        unfold Rminus; rewrite Raxioms.Rplus_0_l.
        apply RIneq.Ropp_lt_gt_0_contravar => //.

        move => NEqa0 /= N.
        replace ɛ with (a * /a * ɛ).
        2 : rewrite RIneq.Rinv_r.
        2 : rewrite Raxioms.Rmult_1_l => //.
        2 : assumption.
        replace (a * l - a * / a * ɛ) with (a * (l - /a * ɛ)).
            2 : rewrite Raxioms.Rmult_plus_distr_l.
            2 : rewrite RIneq.Ropp_mult_distr_r_reverse.
            2 : rewrite Raxioms.Rmult_assoc => //.

        assert (0 < /a * ɛ).
        replace 0 with (/a * 0)%R.
        2 : rewrite RIneq.Rmult_0_r => //.
        apply Raxioms.Rmult_lt_compat_l.
        apply RIneq.Rinv_0_lt_compat.
        case: Ha => //.
        move => Abs; rewrite Abs in NEqa0 => //.
        assumption.
        pose sigɛ' := RIneq.mkposreal (/a * ɛ) H.
        case: (Hl sigɛ') => Hɛ'1 Hɛ'2.
        case: Hɛ'2 => N' HN'.
        assert (N' ≤ max N N') by apply Max.le_max_r.
        case: (Hɛ'1 (max N N')) => N'' [HN'' HN''lt].
        assert (N' ≤ N'').
            apply Nat.le_trans with (max N N') => //.
        pose Ineq := (HN' N'' H1); clearbody Ineq; simpl in Ineq.
        clear HN' H0; simpl in HN''lt.
        exists N''; split; [apply Max.max_lub_l with N' => // | ].
        assert (N' ≤ N'') by apply Max.max_lub_r with N => //.
        case_eq (u N'').
        all : swap 1 2.
        move => Abs.
        rewrite Abs in Ineq => //.
        all : swap 1 2.
        move => Abs.
        rewrite Abs in HN''lt => //.
        move => uN'' EquN'' => /=.
        apply Raxioms.Rmult_lt_compat_l.
        case: Ha => //.
        move => Abs; rewrite Abs in NEqa0 => //.
        rewrite EquN'' in HN''lt => //.

    case: (RIneq.Req_EM_T a 0).
        move => ->; exists O => n _.
        rewrite Rbar_mult_0_l.
        rewrite RIneq.Rmult_0_l.
        unfold Rminus; rewrite Raxioms.Rplus_0_l => //.

        move => NEqa0.
        assert (0 < /a * ɛ).
        replace 0 with (/a * 0)%R.
        2 : rewrite RIneq.Rmult_0_r => //.
        apply Raxioms.Rmult_lt_compat_l.
        apply RIneq.Rinv_0_lt_compat.
        case: Ha => //.
        move => Abs; rewrite Abs in NEqa0 => //.
        assumption.
        pose sigɛ' := RIneq.mkposreal (/a * ɛ) H.
        case: (Hl sigɛ') => Hɛ'1 Hɛ'2.
        case: Hɛ'2 => N' HN' => /=; simpl in HN', Hɛ'1.
        exists N' => n Hn.
        pose Ineq := HN' n Hn; clearbody Ineq.

        replace ɛ with (a * /a * ɛ).
        2 : rewrite RIneq.Rinv_r.
        2 : rewrite Raxioms.Rmult_1_l => //.
        2 : assumption.
        replace (a * l + a * / a * ɛ) with (a * (l + /a * ɛ)).
            2 : rewrite Raxioms.Rmult_plus_distr_l.
            2 : rewrite Raxioms.Rmult_assoc => //.
        rewrite <-Rbar_finite_mult.
        apply Rbar_mult_lt_compat_l.
        case: Ha => //.
        move => Abs; rewrite Abs in NEqa0 => //.
        assumption.
Qed.

Section Boshner_integrable_fun.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope fun_scope.

    (* Bochner Integrable Functions *)
    Inductive Bif (f : X -> E) : Type :=
        | approximation (s : nat -> simpl_fun E μ) :
            inhabited X ->
            (∀ x : X, is_lim_seq (fun n => s n x) (f x))
            -> is_LimSup_seq' (fun n => LInt_p μ (‖ f - (s n) ‖)%fn) 0 -> Bif f.

End Boshner_integrable_fun.

Arguments Bif {X E gen} μ f.

(* On note L¹(X,μ,E) l'espace des fonction Boshner integrable de X vers E *)
Notation "'L¹(' X ',' μ ',' E ')'" := { f : X -> E | Bif μ f }
    (format "'[ ' 'L¹(' X ','  μ ','  E ')' ']'").

Section Bi_fun_prop.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma Cauchy_seq_approx :
        ∀ f : X -> E, ∀ s : nat -> simpl_fun E μ, inhabited X ->
            (∀ x : X, is_lim_seq (fun n => s n x) (f x)) -> is_LimSup_seq' (fun n => LInt_p μ (‖ f - (s n) ‖)%fn) 0 
            -> NM_Cauchy_seq (fun n => BInt_sf (s n)).
    Proof.
        move => f s ι Hspointwise Hs.
        unfold Cauchy_seq => ɛ Hɛ.
        unfold is_LimSup_seq' in Hs.
        pose sighalfɛ := RIneq.mkposreal (ɛ * /2) (R_compl.Rmult_lt_pos_pos_pos _ _ (RIneq.Rgt_lt _ _ Hɛ) RIneq.pos_half_prf).
        case: (Hs sighalfɛ) => [HsMaj {}Hs].
        case: Hs => N HsN.
        exists N.
        move => p q Hp Hq.
        unfold ball_norm.
        unfold minus.
        setoid_rewrite <-(scal_opp_one (BInt_sf (s p))).
        rewrite <-BInt_sf_scal_aux, <-BInt_sf_plus_aux.
        apply RIneq.Rle_lt_trans with (BInt_sf (‖(s q) - (s p)‖)%sf).
            apply norm_Bint_sf_le.
        rewrite (BInt_sf_LInt_SFp).
        rewrite <-LInt_p_SFp_eq.
            2 : exact ι.
            all : swap 1 2.
            unfold sum_Rbar_nonneg.non_neg => x /=.
            rewrite fun_sf_norm.
            apply norm_ge_0.
        assert (∀ x : X, Rbar_le ((‖ s q + (- s p)%sf ‖)%fn x) (((‖ f - s q ‖) + (‖ f - s p ‖))%fn x)).
            move => x; simpl.
            unfold fun_norm, fun_plus.
            do 2 rewrite fun_sf_scal.
            replace (s q x) with ((s q x) + zero)%hy at 1.
                2 : rewrite plus_zero_r => //.
            replace zero with (opp (f x) + f x)%hy at 1.
                2 : apply plus_opp_l.
            rewrite plus_assoc.
            setoid_rewrite plus_comm at 3.
            setoid_rewrite <-norm_opp at 2.
            rewrite opp_plus; setoid_rewrite scal_opp_one at 2.
            rewrite opp_opp; rewrite <-plus_assoc.
            apply norm_triangle.

        pose Ineq := (LInt_p_monotone μ (‖ s q - s p ‖)%fn ((‖ f - s q ‖) + (‖ f - s p ‖))%fn H);
            clearbody Ineq.
        replace ɛ with (real ɛ).
            2 : easy.
        rewrite <-Rbar_lt_finite_eq_rlt.
            3 : easy.
        rewrite (LInt_p_ext _ _ (λ x : X, (‖ s q + (- s p)%sf ‖)%fn x)).
            2 : unfold fun_norm.
            2 : setoid_rewrite fun_sf_norm.
            2 : setoid_rewrite fun_sf_plus => //.
        apply (Rbar_le_lt_trans _ _ (Finite ɛ) Ineq).
        unfold fun_plus at 1.
        rewrite (LInt_p_ext _ _ (λ x : X, Rbar_plus ((‖ f + (- s q)%sf ‖)%fn x) ((‖ f + (- s p)%sf ‖)%fn x)%hy)).
            2 : by [].
        rewrite LInt_p_plus.
            2 : exact ι.
            2, 4 : unfold sum_Rbar_nonneg.non_neg => x.
            2, 3 : unfold fun_norm; apply norm_ge_0.
        replace ɛ with (real (Rbar_plus (ɛ*/2) (ɛ*/2))).
        clear H Ineq.
        unfold "_ - _" in HsN.
        simpl in HsN.
        rewrite Raxioms.Rplus_0_l in HsN.
        apply (Rbar_plus_lt_compat (LInt_p μ (λ x : X, (‖ f + (- s q)%sf ‖)%fn x)) (ɛ*/2) 
                                    (LInt_p μ (λ x : X, (‖ f + (- s p)%sf ‖)%fn x)) (ɛ*/2)).
            1, 2 :apply HsN => //.
            simpl; rewrite Rlimit.eps2 => //.
        all : swap 1 3.
        pose Lint_p_Bint_sf :=
            Finite_BInt_sf_LInt_SFp (‖ s q - s p ‖)%sf.
            rewrite <-LInt_p_SFp_eq in Lint_p_Bint_sf.
            2 : exact ι.
            2 : unfold sum_Rbar_nonneg.non_neg => x.
            2 : simpl; rewrite fun_sf_norm.
            2 : apply norm_ge_0.
            rewrite <-Lint_p_Bint_sf => //.

        assert
            (∀ x : X, is_lim_seq (fun n => (‖ s n + (- s p)%sf ‖)%fn x) ((‖ f + (- s p)%sf ‖)%fn x)) as Limseqnorm.
            move => x; unfold fun_norm.
            apply lim_seq_norm.
            apply lim_seq_plus.
            apply Hspointwise.
            apply lim_seq_cte.
        apply measurable_fun_ext with (fun x : X => (Lim_seq' (λ n : nat, (‖ s n + (- s p)%sf ‖)%fn x))).
            move => x; rewrite <-Lim_seq_seq'.
            apply is_lim_seq_unique.
            apply Limseqnorm.
        apply measurable_fun_Lim_seq'.
        move => n; unfold sum_Rbar_nonneg.non_neg => x; apply norm_ge_0.
        move => n; apply measurable_fun_R_Rbar.
        
        apply: (measurable_fun_composition _ open).
        apply measurable_fun_ext with ((s n + (- s p)%sf))%sf.
            move => x.
            rewrite fun_sf_plus => //.
        apply (measurable_fun_sf (s n - s p)%sf).
        move => P. move /sigma_algebra_R_Rbar_new.measurable_R_equiv_oo.
        apply measurable_fun_continuous.
        apply filterlim_norm.

        assert
            (∀ x : X, is_lim_seq (fun n => (‖ s n + (- s q)%sf ‖)%fn x) ((‖ f + (- s q)%sf ‖)%fn x)) as Limseqnorm.
            move => x; unfold fun_norm.
            apply lim_seq_norm.
            apply lim_seq_plus.
            apply Hspointwise.
            apply lim_seq_cte.
        apply measurable_fun_ext with (fun x : X => (Lim_seq' (λ n : nat, (‖ s n + (- s q)%sf ‖)%fn x))).
            move => x; rewrite <-Lim_seq_seq'.
            apply is_lim_seq_unique.
            apply Limseqnorm.
        apply measurable_fun_Lim_seq'.
        move => n; unfold sum_Rbar_nonneg.non_neg => x; apply norm_ge_0.
        move => n; apply measurable_fun_R_Rbar.

        apply: (measurable_fun_composition _ open).
        apply measurable_fun_ext with ((s n + (- s q)%sf))%sf.
            move => x.
            rewrite fun_sf_plus => //.
        apply (measurable_fun_sf (s n - s q)%sf).
        move => P. move /sigma_algebra_R_Rbar_new.measurable_R_equiv_oo.
        apply measurable_fun_continuous.
        apply filterlim_norm.
    Qed.
        
End Bi_fun_prop.

Declare Scope Bif_scope.
Delimit Scope Bif_scope with Bif.

Section Bif_sf.

    (* espace de départ *)
    Context {X : Set}.
    Context (ι : inhabited X).
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Definition Bif_sf (s : simpl_fun E μ) : Bif μ s.
    (* Definition *)
        pose s' := fun _ : nat => s.
        apply (approximation s s').
            exact ι.
            move => x; apply lim_seq_cte.
            unfold s'; unfold fun_norm;
            unfold fun_plus.
            apply is_LimSup_seq'_ext with (fun _ : nat => 0%R).
                move => _; rewrite (LInt_p_ext _ _ (fun x : X => 0)).
                rewrite LInt_p_0 => //.
                move => x; rewrite fun_sf_scal.
                rewrite scal_opp_one plus_opp_r.
                rewrite norm_zero => //.
        apply LimSup_seq'_const.
    Defined.

End Bif_sf.

Section Bif_op.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.
    Context {f g : X -> E}.

    Definition Bif_plus (bf : Bif μ f) (bg : Bif μ g) : Bif μ (f + g)%fn.
        case: bf => sf ι Hfpw Hfl1;
        case: bg => sg _ Hgpw Hgl1.
        apply: (approximation (f + g)%fn (fun n : nat => sf n + sg n)%sf).
            exact ι.
            move => x; unfold fun_plus.
            apply (lim_seq_ext (fun n => sf n x + sg n x)%hy).
                move => n; rewrite fun_sf_plus => //.
            apply: lim_seq_plus => //.
        (**)
        unfold is_LimSup_seq' => ɛ; split; swap 1 2.
        simpl; rewrite Raxioms.Rplus_0_l.
        (**)
        2 : move => N0.
        2 : exists N0; split => //.
        2 : case: ɛ => [ɛ Hɛ].
        2 : unfold Rminus.
        2 : replace (RIneq.pos {| RIneq.pos := ɛ; RIneq.cond_pos := Hɛ |}) with ɛ by move => //.
        2 : setoid_rewrite Raxioms.Rplus_0_l.
        2 : apply Rbar_lt_le_trans with 0%R.
        2 : apply RIneq.Ropp_lt_gt_0_contravar => //.
        2 : apply LInt_p_ge_0 => //; unfold sum_Rbar_nonneg.non_neg.
        2 : move => x; apply norm_ge_0.
        (**)  
        case: ɛ => [ɛ Hɛ].
        pose sighalfɛ := RIneq.mkposreal (ɛ * /2) (R_compl.Rmult_lt_pos_pos_pos _ _ (RIneq.Rgt_lt _ _ Hɛ) RIneq.pos_half_prf).
        case: (Hfl1 sighalfɛ) => [HfMaj {}Hf].
        case: (Hgl1 sighalfɛ) => [HgMaj {}Hg].
        case: Hf => N HfN.
        case: Hg => N' HgN'.
        exists (max N N').
        move => n Hn => /=.
        unfold minus.
        (**)
        assert (∀ x : X,
                    Rbar_le
                    ((λ x0 : X, (‖ f + g + (- (sf n + sg n))%sf ‖)%fn x0) x)
                    ((λ x0 : X,
                        ((‖ f + (- sf n)%sf ‖) + (‖ g + (- sg n)%sf ‖))%fn x0) x)).
            move => x; simpl.
            unfold fun_norm, fun_plus.
            do 3 rewrite fun_sf_scal.
            setoid_rewrite scal_opp_one.
            rewrite fun_sf_plus;
            rewrite opp_plus;
            rewrite plus_comm;
            rewrite <-plus_assoc;
            setoid_rewrite plus_comm at 2;
            rewrite <-plus_assoc;
            rewrite plus_comm;
            setoid_rewrite plus_comm at 2;
            rewrite <-plus_assoc;
            rewrite plus_comm.
            apply norm_triangle.
        (**)
        pose Ineq := (LInt_p_monotone μ (λ x : X, (‖ f + g + (- (sf n + sg n))%sf ‖)%fn x) ((‖ f - sf n ‖) + (‖ g - sg n ‖))%fn H);
            clearbody Ineq.
        replace ɛ with (real ɛ).
            2 : easy.
        apply (Rbar_le_lt_trans _ _ (Finite ɛ) Ineq).
        unfold fun_plus at 1.
        rewrite (LInt_p_ext _ _ (λ x : X, Rbar_plus ((‖ f + (- sf n)%sf ‖)%fn x) ((‖ g + (- sg n)%sf ‖)%fn x)%hy)).
            2 : by [].
        rewrite LInt_p_plus.
            2 : exact ι.
            2, 4 : unfold sum_Rbar_nonneg.non_neg => x.
            2, 3 : unfold fun_norm; apply norm_ge_0.
        replace ɛ with (real (Rbar_plus (ɛ*/2) (ɛ*/2))).
        clear H Ineq.
        unfold "_ - _" in HfN.
        simpl in HfN, HgN'.
        rewrite Raxioms.Rplus_0_l in HfN.
        rewrite Raxioms.Rplus_0_l in HgN'.
        apply (Rbar_plus_lt_compat (LInt_p μ (λ x : X, (‖ f + (- sf n)%sf ‖)%fn x)) (ɛ*/2) 
                                    (LInt_p μ (λ x : X, (‖ g + (- sg n)%sf ‖)%fn x)) (ɛ*/2)).
            apply HfN; apply Max.max_lub_l with N' => //.
            apply HgN'; apply Max.max_lub_r with N => //.
            simpl; rewrite Rlimit.eps2 => //.
        all : swap 1 3.
        (**)
        clear Ineq.
        assert
            (∀ x : X, is_lim_seq (fun k => (‖ sf k + (- sf n)%sf ‖)%fn x) ((‖ f + (- sf n)%sf ‖)%fn x)) as Limseqnorm.
            move => x; unfold fun_norm.
            apply lim_seq_norm.
            apply lim_seq_plus.
            apply Hfpw.
            apply lim_seq_cte.
        apply measurable_fun_ext with (fun x : X => (Lim_seq' (λ k : nat, (‖ sf k + (- sf n)%sf ‖)%fn x))).
            move => x; rewrite <-Lim_seq_seq'.
            apply is_lim_seq_unique.
            unfold Lim_seq.is_lim_seq.
            unfold Rbar_locally => /=.
            apply: Limseqnorm.
        apply measurable_fun_Lim_seq'.
        move => k; unfold sum_Rbar_nonneg.non_neg => x; apply norm_ge_0.
        move => k; apply measurable_fun_R_Rbar.
        (**) 
        apply: (measurable_fun_composition _ open).
        apply measurable_fun_ext with ((sf k + (- sf n)%sf))%sf.
            move => x.
            rewrite fun_sf_plus => //.
        apply (measurable_fun_sf (sf k - sf n)%sf).
        move => P; move /sigma_algebra_R_Rbar_new.measurable_R_equiv_oo.
        apply measurable_fun_continuous.
        apply filterlim_norm.
        (**)
        assert
            (∀ x : X, is_lim_seq (fun k => (‖ sg k + (- sg n)%sf ‖)%fn x) ((‖ g + (- sg n)%sf ‖)%fn x)) as Limseqnorm.
            move => x; unfold fun_norm.
            apply lim_seq_norm.
            apply lim_seq_plus.
            apply Hgpw.
            apply lim_seq_cte.
        apply measurable_fun_ext with (fun x : X => (Lim_seq' (λ k : nat, (‖ sg k + (- sg n)%sf ‖)%fn x))).
            move => x; rewrite <-Lim_seq_seq'.
            apply is_lim_seq_unique.
            unfold Lim_seq.is_lim_seq.
            unfold Rbar_locally => /=.
            apply: Limseqnorm.
        apply measurable_fun_Lim_seq'.
        move => k; unfold sum_Rbar_nonneg.non_neg => x; apply norm_ge_0.
        move => k; apply measurable_fun_R_Rbar.
        (**) 
        apply: (measurable_fun_composition _ open).
        apply measurable_fun_ext with ((sg k + (- sg n)%sf))%sf.
            move => x.
            rewrite fun_sf_plus => //.
        apply (measurable_fun_sf (sg k - sg n)%sf).
        move => P; move /sigma_algebra_R_Rbar_new.measurable_R_equiv_oo.
        apply measurable_fun_continuous.
        apply filterlim_norm.
    Defined.

    Definition Bif_scal (a : R_AbsRing) (bf : Bif μ f) : Bif μ (a ⋅ f)%fn.
    (* Definition *)
        case_eq bf => sf ι Hfpw Hfl1 Eqf.
        apply: (approximation (a ⋅ f)%fn (fun n : nat => a ⋅ sf n)%sf).
            exact ι.
            move => x; unfold fun_scal.
            apply (lim_seq_ext (fun n => a ⋅ sf n x)%hy).
                move => n; rewrite fun_sf_scal => //.
            apply: lim_seq_scal_r => //.
        (**)
        apply is_LimSup_seq'_ext with (fun n => Rbar_mult (| a |)%hy (LInt_p μ (‖ f - sf n ‖)%fn)).
            move => n; unfold fun_norm, fun_plus, fun_scal.
            rewrite <-LInt_p_scal => //.
                all : swap 1 2.
                unfold sum_Rbar_nonneg.non_neg => x; apply norm_ge_0.
            apply LInt_p_ext => x; do 2 rewrite fun_sf_scal.
            do 2 rewrite scal_opp_one; rewrite fun_sf_scal; rewrite <-scal_opp_r.
            replace (a ⋅ f x + a ⋅ opp (sf n x))%hy with
                (a ⋅ (f x + opp (sf n x)))%hy at 1
                by rewrite scal_distr_l => //.
            rewrite norm_scal_eq => //.
            2 : apply Rabs_pos.
            assert
                (∀ x : X, is_lim_seq (fun k => (‖ sf k + (- sf n)%sf ‖)%fn x) ((‖ f + (- sf n)%sf ‖)%fn x)) as Limseqnorm.
                move => x; unfold fun_norm.
                apply lim_seq_norm.
                apply lim_seq_plus.
                apply Hfpw.
                apply lim_seq_cte.
            apply measurable_fun_ext with (fun x : X => (Lim_seq' (λ k : nat, (‖ sf k + (- sf n)%sf ‖)%fn x))).
                move => x; rewrite <-Lim_seq_seq'.
                apply is_lim_seq_unique.
                unfold Lim_seq.is_lim_seq.
                unfold Rbar_locally => /=.
                apply: Limseqnorm.
            apply measurable_fun_Lim_seq'.
            move => k; unfold sum_Rbar_nonneg.non_neg => x; apply norm_ge_0.
            move => k; apply measurable_fun_R_Rbar.
            (**)     
            apply: (measurable_fun_composition _ open).
            apply measurable_fun_ext with ((sf k + (- sf n)%sf))%sf.
                move => x.
                rewrite fun_sf_plus => //.
            apply (measurable_fun_sf (sf k - sf n)%sf).
            move => P; move /sigma_algebra_R_Rbar_new.measurable_R_equiv_oo.
            apply measurable_fun_continuous.
            apply filterlim_norm.
            (**)
            assert (Rbar_mult (|a|)%hy 0 = 0).
            unfold Rbar_mult => /=.
            rewrite RIneq.Rmult_0_r => //.
            (**)
            rewrite <-H.
            apply is_LimSup_seq'_scal_l.
            apply abs_ge_0.
            assumption.
    Defined.

    Definition Bif_norm (bf : Bif μ f) : Bif μ (‖f‖)%fn.
    (* Definition *)
        case_eq bf => sf ι Hfpw Hfl1 Eqf.
        apply: (approximation (‖f‖)%fn (fun n : nat => ‖ sf n ‖)%sf).
            exact ι.
            move => x; unfold fun_norm.
            apply (lim_seq_ext (fun n => ‖ sf n x ‖ )%hy).
                move => n; rewrite fun_sf_norm => //.
            apply: lim_seq_norm => //.
        (* *)     
        unfold is_LimSup_seq'; move => [ɛ Hɛ]; split; swap 1 2.
        simpl; rewrite Raxioms.Rplus_0_l.
        (**)
        2 : move => N0.
        2 : exists N0; split => //.
        2 : unfold Rminus.
        2 : replace (RIneq.pos {| RIneq.pos := ɛ; RIneq.cond_pos := Hɛ |}) with ɛ by move => //.
        2 : setoid_rewrite Raxioms.Rplus_0_l.
        2 : apply Rbar_lt_le_trans with 0%R.
        2 : apply RIneq.Ropp_lt_gt_0_contravar => //.
        2 : apply LInt_p_ge_0 => //; unfold sum_Rbar_nonneg.non_neg.
        2 : move => x; apply norm_ge_0.
        (**)
        case: (Hfl1 (RIneq.mkposreal ɛ Hɛ)) => Hɛ1 Hɛ2.
        case: Hɛ2 => N HN.
        exists N => n Hn.
        apply Rbar_le_lt_trans with (LInt_p μ (λ x : X, (‖ f + (- sf n)%sf ‖)%fn x)); swap 1 2.
            simpl in HN; rewrite Raxioms.Rplus_0_l in HN.
            apply HN => //.
        apply LInt_p_monotone => x.
        unfold fun_norm at 1.
        unfold norm at 1 => /=.
        unfold fun_plus.
        unfold fun_norm.
        rewrite fun_sf_scal scal_opp_one.
        rewrite fun_sf_norm.
        rewrite fun_sf_scal scal_opp_one.
        replace ((‖ f x ‖) + opp (‖ sf n x ‖))%hy with (minus (‖ f x ‖)%hy (‖ sf n x ‖)%hy) at 1
            by unfold minus => //.
        replace (f x + opp (sf n x))%hy with (minus (f x) (sf n x))%hy at 1
            by unfold minus => //.
        apply: norm_triangle_inv.
    Defined.

End Bif_op.

Notation "bf + bg" := (Bif_plus bf bg) : Bif_scope.
Notation "a ⋅ bf" := (Bif_scal a bf) : Bif_scope.
Notation "‖ bf ‖" := (Bif_norm bf) : Bif_scope.

Definition inRange 
    {X : Set} {A : AbsRing} {E : NormedModule A}
    (g : X -> E) : E -> Prop :=
        fun y => ∃ x : X, g x = y.

Lemma iRR {X : Set} {A : AbsRing} {E : NormedModule A} 
    : ∀ g : X -> E, ∀ x : X, inRange g (g x).
Proof.
    move => g x; exists x => //.
Qed.

Module Bif_adapted_seq.

    Section construction_of_seq.

        (* espace de départ *)
        Context {X : Set}.
        (* espace d'arrivé *)
        Context {E : CompleteNormedModule R_AbsRing}.
        (* Un espace mesuré *)
        Context {gen : (X -> Prop) -> Prop}.
        Context {μ : measure gen}.
        Context {f : X -> E}.
        
        Context {u : nat -> E}.
        Context {φ : ∀ x : E, inRange f x -> RIneq.posreal -> nat}.
        Context (Hsep : fun_separable u (inRange f) φ).

        Definition B (m : nat) (j : nat) :=
            ball_norm (u j) (/ (INR m + 1)).
        
        Definition A (n : nat) := fun x =>
            ∃ j : nat, (j < n)%nat ∧ B n j x.

        Lemma measB : ∀ m j, measurable open (B m j).
        Proof.
            move => m j; unfold B.
            assert (0 < (/ (INR m + 1)))
                by apply RiemannInt.RinvN_pos.
            constructor 1; apply NM_open_ball_norm => //.
        Qed.

        Lemma measA : ∀ n, measurable open (A n).
        Proof.
            Print Implicit measurable_union_finite'.
            unfold A => n; apply: measurable_union_finite'.
            move => j _; apply measB.
        Qed.

        Lemma decB (m j : nat) (x : E) :
            {B m j x} + {¬ B m j x}.
        Proof.
            unfold B.
            assert (0 < (/ (INR m + 1)))
                by apply RiemannInt.RinvN_pos.
            pose ɛ := RIneq.mkposreal (/ (INR m + 1)) H.
            pose Hdec := (ball_norm_dec (u j) x ɛ).
            simpl in Hdec => //.
        Qed.

        Close Scope R_scope.

        Lemma LPO_min_finite :
            ∀ m : nat, ∀ P : nat -> Prop,
                (∀ j : nat, (j < m) -> {P j} + {¬ P j})
                ->  { j : nat 
                        | (j < m) 
                        ∧ P j 
                        ∧ (∀ i : nat, (i < j) -> ¬ P i) 
                    } 
                    + 
                    { ∀ j : nat, (j < m) -> ¬ P j }.
        Proof.
            move => m P HP.
            pose Q := (fun i => (i < m)%nat ∧ P i).
            assert ({j : nat | Q j ∧ ∀ i, (i < j)%nat → ¬ Q i} + {∀ j, ¬ Q j}).
            apply LPO_min => j; unfold Q.
            case_eq (j <? m).
                move => /Nat.ltb_lt Hj.
                case: (HP j Hj).
                    move => Pj; left; split => //.
                    move => NPj; right; case => _ /NPj//.
                move => /Nat.ltb_ge Hj; right; case; lia.
            case: H.
                case => j; unfold Q; case; move => [Ltjm Pj] HQ; left.
                exists j; repeat split => //.
                move => i Hi Pi.
                assert (i < m)%nat by lia.
                apply HQ with i => //.
            move => H; right; unfold Q in H.
            move => j Hj Pj.
            apply H with j => //.
        Qed.

        Lemma LPO_min_finite_decr :
            ∀ m : nat, ∀ P : nat -> Prop,
                (∀ j : nat, (j < m) -> {P j} + {¬ P j})
                ->  { j : nat 
                        | (j < m) 
                        ∧ P j 
                        ∧ (∀ i : nat, (i > j) -> (i < m) -> ¬ P i) 
                    } 
                    + 
                    { ∀ j : nat, (j < m) -> ¬ P j }.
        Proof.
            move => m P HP.
            pose Q := (fun i => (i < m)%nat ∧ P (m - (S i))%nat).
            assert ({j : nat | Q j ∧ ∀ i, (i < j)%nat → ¬ Q i} + {∀ j, ¬ Q j}).
            apply LPO_min => j; unfold Q.
            case_eq (j <? m).
                move => /Nat.ltb_lt Hj.
                assert (m - S j < m)%nat as Hj' by lia.
                case: (HP (m - S j)%nat Hj').
                    move => Pj; left; split => //.
                    move => NPj; right; case => _ /NPj//.
                move => /Nat.ltb_ge Hj; right; case; lia.
            case: H.
                case => j; unfold Q; case; move => [Ltjm Pm1j] HQ; left.
                exists (m - S j)%nat; repeat split => //.
                lia.
                move => i Hi1 Hi2 Pi.
                assert (m - S i < m)%nat by lia.
                apply HQ with (m - S i)%nat => //.
                lia.
                split. 
                lia.
                replace (m - S (m - S i))%nat with i by lia.
                assumption.
            move => H; right; unfold Q in H.
            move => j Hj Pj.
            apply H with (m - S j)%nat; split.
            lia.
            replace (m - S (m - S j))%nat with j by lia.
            assumption.
        Qed.

        Lemma decA (n : nat) (x : E) :
            {A n x} + {¬ A n x}.
        Proof.
            assert (∀ j : nat,
                (j < n)%nat → {(λ j0 : nat, B n j0 x) j} + {¬ (λ j0 : nat, B n j0 x) j}).
                move => j _; apply decB.
            unfold A; case : (LPO_min_finite n (fun j => B n j x) H).
            case => j [Hj [Bnjx HB]]; left; exists j; split => //.
            move => Hj; right; case => j; case; move => /Hj//.
        Qed.

        Lemma decA_aux (max : nat) (x : E) : ∀ j : nat,
            (j < max) -> {A j x} + {¬ A j x}.
        Proof.
            move => j _; apply decA.
        Qed.

        Definition biggestA (max : nat) (x : E) : nat :=
            match LPO_min_finite_decr max (fun j => A j x) (decA_aux max x) with
                | inleft e => proj1_sig e
                | inright _ => max
            end.

        Lemma biggestA_le_max (max : nat) (x : E) :
            biggestA max x ≤ max.
        Proof.
            unfold biggestA.
            case_eq (LPO_min_finite_decr max (λ j : nat, A j x) (decA_aux max x)).
                move => s EqLPO.
                case_eq s => j [Ltjmax H] => /=.
                lia.
                easy.
        Qed.

        Lemma decB_aux (m : nat) (x : E) : ∀ j : nat,
            (j < m) -> {B m j x} + {¬ B m j x}.
        Proof.
            move => j _; apply decB.
        Qed.

        Definition smallestB (max : nat) (m : nat) (x : E) : nat :=
            match LPO_min_finite m (fun j => B m j x) (decB_aux m x) with
                | inleft e => proj1_sig e
                | inright _ => max
            end.

        Lemma smallestB_le_n (max : nat) (m : nat) (x : E) :
            m ≤ max -> smallestB max m x = max ∨ smallestB max m x < m.
        Proof.
            move => Lemmax.
            unfold smallestB.
            case (LPO_min_finite m (λ j : nat, B m j x) (decB_aux m x)).
            case => j /=; lia.
            left; easy.
        Qed.

        Lemma smallestB_le_n_weak (max : nat) (m : nat) (x : E) :
            m ≤ max -> smallestB max m x ≤ max.
        Proof.
            move => Lemmax.
            case: (smallestB_le_n max m x) => //.
            1, 2 : lia.
        Qed.

        Lemma smallestB_le_n_strong (max : nat) (m : nat) (x : E) :
            m ≤ max -> smallestB max m x < max -> smallestB max m x < m.
        Proof.
            move => Lemmax HsmallB.
            pose H := smallestB_le_n max m x Lemmax; clearbody H.
            lia.
        Qed.

        Definition whichn' (n : nat) := fun x =>
            let m := biggestA n x in
            if (m =? n) then n else
                smallestB n m x.

        Lemma whichn'_le_n (n : nat) (x : E) :
            whichn' n x ≤ n.
        Proof.
            unfold whichn'.
            case (biggestA n x =? n) => //.
            apply smallestB_le_n_weak.
            apply biggestA_le_max.
        Qed.

        Lemma biggestA_lt_max_spec (n : nat) (m : nat) : (m < n) ->
            ∀ x : E,
            biggestA n x = m <-> (A m x ∧ (∀ j : nat, j > m -> j < n -> ¬ A j x)).
        Proof.
            move => Ltmn x; split.
            move => Eqwnxm; rewrite <-Eqwnxm in Ltmn.
            unfold whichn' in Ltmn, Eqwnxm.
            unfold biggestA in Ltmn, Eqwnxm.
            case_eq (LPO_min_finite_decr n (λ j : nat, A j x) (decA_aux n x)).
                move => s EqLPO; rewrite EqLPO in Ltmn, Eqwnxm.
                case_eq s => j [Hj1 [Hj2 Hj3]] Eqs.
                rewrite Eqs in Ltmn, Eqwnxm.
                simpl in Ltmn, Eqwnxm.
                rewrite <-Eqwnxm.
                repeat split => //.
                move => HNA EqLPO; rewrite EqLPO in Ltmn, Eqwnxm.
                lia.
            case => Amx HNA.
            unfold biggestA.
            case (LPO_min_finite_decr n (λ j : nat, A j x) (decA_aux n x)).
                case => j [Hj1 [Hj2 Hj3]] => /=.
                case: (lt_eq_lt_dec j m).
                case => //.
                move =>/(Hj3 _) Hj.
                move: Ltmn => /Hj Abs.
                apply False_ind, Abs => //.
                move => /HNA Hj.
                move: Hj1 => /Hj Abs.
                apply False_ind, Abs => //.
                move => Abs.
                apply False_ind.
                pose Absm := Abs m Ltmn => //.
        Qed.

        Lemma biggestA_eq_max_spec (n : nat) :
            ∀ x : E,
            biggestA n x = n <-> (∀ j : nat, j < n -> ¬ A j x).
        Proof.
            move => x; split.
                move => HbigA.
                unfold biggestA in HbigA.
                case_eq (LPO_min_finite_decr n (λ j : nat, A j x) (decA_aux n x)).
                    move => s EqLPO.
                    rewrite EqLPO in HbigA.
                    case_eq s.
                    move => j [Hj1 [Hj2 Hj3]] Eqs.
                    rewrite Eqs in HbigA.
                    simpl in HbigA.
                    lia.
                    move => HNA.
                    easy.
                move => HNA.
                unfold biggestA.
                case: (LPO_min_finite_decr n (λ j : nat, A j x) (decA_aux n x)).
                    case => j [Hj1 [Hj2 Hj3]] => /=.
                    apply False_ind.
                    pose Abs := HNA j Hj1.
                    apply Abs => //.
                    easy.
        Qed.

        Lemma smallestB_lt_max_spec (max : nat) (m : nat) (j : nat) : (m ≤ max) -> (j < m) ->
            ∀ x : E,
            smallestB max m x = j <-> (B m j x ∧ (∀ i : nat, i < j -> ¬ B m i x)).
        Proof.
            move => Lemmax Ltjm x; split.
                move => HsmallB.
                unfold smallestB in HsmallB.
                case_eq (LPO_min_finite m (λ j : nat, B m j x) (decB_aux m x)).
                    move => s EqLPO.
                    case_eq s => i [Hi1 [Hi2 Hi3]] Eqs.
                    rewrite EqLPO in HsmallB.
                    rewrite Eqs in HsmallB.
                    simpl in HsmallB.
                    rewrite <-HsmallB.
                    repeat split => //.
                    move => Hj EqLPO.
                    rewrite EqLPO in HsmallB.
                    lia.
                case => Bmjx Hj.
                unfold smallestB.
                case: (LPO_min_finite m (λ j0 : nat, B m j0 x) (decB_aux m x)).
                    case => /= j' [Hj'1 [Hj'2 Hj'3]].
                    case: (lt_eq_lt_dec j j').
                    case => //.
                    move => /Hj'3//.
                    move => /Hj//.
                    move => Hj'.
                    apply False_ind.
                    apply (Hj' j Ltjm) => //.
        Qed.

        Lemma smallestB_eq_max_spec (max : nat) (m : nat) : (m ≤ max) ->
            ∀ x : E,
            smallestB max m x = max <-> (∀ j : nat, j < m -> ¬ B m j x).
        Proof.
            move => Lemmax x; split.
                move => HsmallB.
                unfold smallestB in HsmallB.
                case_eq (LPO_min_finite m (λ j : nat, B m j x) (decB_aux m x)).
                    move => s EqLPO.
                    case_eq s.
                    move => j [Hj1 [Hj2 Hj3]] Eqs.
                    rewrite EqLPO in HsmallB.
                    rewrite Eqs in HsmallB.
                    simpl in HsmallB.
                    lia.
                    easy.
                move => HNB.
                unfold smallestB.
                case: (LPO_min_finite m (λ j : nat, B m j x) (decB_aux m x)).
                    case => j [Hj1 [Hj2 Hj3]] /=.
                    apply False_ind.
                    move: Hj1 => /HNB//.
                    easy.
        Qed.

        Lemma whichn'_spec_lt_n (n : nat) (j : nat) : (j < n) ->
            ∀ x : E,
            whichn' n x = j <->
            ∃ m : nat, m < n ∧
            (
                (A m x ∧ ¬ (∃ k : nat, k > m ∧ k < n ∧ A k x)) ∧
                ((B m j x) ∧ ¬ (∃ i : nat, i < j ∧ B m i x))
            ).
        Proof.
            pose LebigAn := biggestA_le_max n; clearbody LebigAn.
            move => Ltjn x; split.
                unfold whichn'.
                case_eq (biggestA n x =? n).
                lia.
                move => /Nat.eqb_neq.
                move => HbigA.
                pose HbigA' := LebigAn x; clearbody HbigA'.
                assert (biggestA n x < n) as LtbigA by lia.
                move => HsmallB.
                assert (smallestB n (biggestA n x) x < n) by lia.
                pose H' := (smallestB_le_n_strong n (biggestA n x) x HbigA' H); clearbody H'.
                rewrite HsmallB in H'.
                pose specB := smallestB_lt_max_spec n (biggestA n x) j HbigA' H' x.
                case: specB => [specB _].
                move: HsmallB => /specB [specB1 specB2].
                exists (biggestA n x).
                repeat split => //.
                1, 2 : case: (biggestA_lt_max_spec _ _ LtbigA x) => [HA _].
                1, 2 : assert (biggestA n x = biggestA n x) by easy.
                1, 2 : move: H0 => /HA.
                case => //.
                case => _ HNA.
                case => i [Hi1 [Hi2 Hi3]].
                apply HNA with i => //.
                case => i [Hi1 Hi2].
                apply specB2 with i => //.

                case => m [Ltmn [[Amx HNA] [Bmjx HNB]]].
                unfold whichn'.
                assert (biggestA n x < n) as LtbigA.
                pose LebigAnx := LebigAn x; clearbody LebigAnx; clear LebigAn.
                case: (le_lt_or_eq _ _ LebigAnx) => //.
                move /biggestA_eq_max_spec => Abs.
                pose Absm := Abs m Ltmn; clearbody Absm => //.
                assert (biggestA n x ≠ n) as NeqbigA by lia.
                move: NeqbigA => /Nat.eqb_neq ->.
                assert (m ≤ n) as Lemn by lia.
                assert (smallestB n m x < n).
                case: (smallestB_le_n _ _ x Lemn).
                    2 : lia.
                move => /(smallestB_eq_max_spec n m Lemn) Abs; apply False_ind.
                assert (j < m) as Ltjm.
                assert (j < m ∨ j ≥ m) by lia.
                case: H => //.
                move => Lemj; apply False_ind.
                case: Amx => i; case => /(Abs i)//.
                apply: (Abs j) => //.
                move: H => /(smallestB_le_n_strong n m x Lemn) LtsmallBm.
                assert (smallestB n m x = smallestB n m x) by easy.
                move: H => /(smallestB_lt_max_spec n m (smallestB n m x) Lemn LtsmallBm x) [Bmsx HNB'].
                assert (biggestA n x = m) as Eqm.
                assert (biggestA n x = biggestA n x) as H by easy.
                move: H => /((biggestA_lt_max_spec) n _ LtbigA x); move => [AbigAx HNA'].
                case (lt_eq_lt_dec (biggestA n x) m).
                case => //.
                move => /(fun k => HNA' m k Ltmn)//.
                move => Abs; apply False_ind, HNA.
                exists (biggestA n x); repeat split => //.
                rewrite Eqm.
                case (lt_eq_lt_dec (smallestB n m x) j).
                case => //.
                move => Abs; apply False_ind, HNB.
                exists (smallestB n m x); repeat split => //.
                move => /(HNB' j)//.
        Qed.

        Lemma whichn'_spec_eq_n (n : nat) :
            ∀ x : E,
            whichn' n x = n <-> (¬ ∃ m : nat, m < n ∧ A m x).
        Proof.
            move => x; split.
                move => Hwnx.
                unfold whichn' in Hwnx.
                case_eq (biggestA n x =? n).
                    move => /Nat.eqb_eq HbigA.
                    clear Hwnx.
                    unfold biggestA in HbigA.
                    case_eq (LPO_min_finite_decr n (λ j : nat, A j x) (decA_aux n x)).
                        2 : move => HNA _; case => j; case => /HNA//.
                        move => s EqLPO.
                        rewrite EqLPO in HbigA.
                        case_eq s => j [Abs H] Eqs.
                        rewrite Eqs in HbigA.
                        simpl in HbigA.
                        lia.
                    move => HbigA; rewrite HbigA in Hwnx.
                    move: HbigA => /Nat.eqb_neq HbigA.
                    unfold smallestB in Hwnx.
                    case_eq (LPO_min_finite (biggestA n x) (λ j : nat, B (biggestA n x) j x)
                        (decB_aux (biggestA n x) x)).
                        move => s EqLPO.
                        rewrite EqLPO in Hwnx.
                        case_eq s => j [Abs H] Eqs.
                        rewrite Eqs in Hwnx.
                        simpl in Hwnx.
                        apply False_ind.
                        unfold biggestA in HbigA.
                        assert (biggestA n x ≤ n) by apply biggestA_le_max.
                        lia.
                        move => HA /= _; clear Hwnx.
                        assert (biggestA n x < n).
                            pose H := biggestA_le_max n x; clearbody H.
                            lia.
                        move => Abs.
                        move: H => /(fun H => biggestA_lt_max_spec n _ H x); case => H _.
                        assert (biggestA n x = biggestA n x) as TrivEq by easy.
                        move: TrivEq => /H; clear H; case => [AbigAx HNA].
                        case: AbigAx => j [LtjbigAx BbigAxjx].
                        apply HA with j => //.

                move => NHA.
                case: (le_lt_or_eq _ _ (whichn'_le_n n x)) => //.
                move => Abs; apply False_ind.
                assert (whichn' n x = whichn' n x) as TrivEq by easy.
                move: TrivEq => / (whichn'_spec_lt_n n (whichn' n x) Abs x); case => j [Ltjn [[Ajx _] _]].
                apply: NHA; exists j; split => //.
        Qed.

        Open Scope R_scope.
        Print Implicit RiemannInt.RinvN_pos.

        Definition whichn (n : nat) (x : X) : nat :=
            let ɛ := (RIneq.mkposreal (/(INR n + 1)) (RiemannInt.RinvN_pos n)) in
            match ball_norm_dec zero (f x) ɛ with
                | left _ => n
                | right _ => whichn' n (f x)
            end.

        Lemma whichn_spec_lt_n (n : nat) (j : nat) : (j < n)%nat ->
            ∀ x : X,
            whichn n x = j <-> (¬ (ball_norm zero (/(INR n + 1)) (f x))) ∧
            ∃ m : nat, (m < n)%nat ∧
            (
                (A m (f x) ∧ ¬ (∃ k : nat, (k > m)%nat ∧ (k < n)%nat ∧ A k (f x))) ∧
                ((B m j (f x)) ∧ ¬ (∃ i : nat, (i < j)%nat ∧ B m i (f x)))
            ).
        Proof.
            move => Ltjn x; split.
                move => Hwhichn; split.
                move => Abs.
                unfold whichn in Hwhichn.
                case_eq (ball_norm_dec zero (f x)  {|
                    RIneq.pos := / (INR n + 1);
                    RIneq.cond_pos := RiemannInt.RinvN_pos n |}).
                    move => H Eqball.
                    rewrite Eqball in Hwhichn.
                    lia.
                case_eq (ball_norm_dec zero (f x)  {|
                    RIneq.pos := / (INR n + 1);
                    RIneq.cond_pos := RiemannInt.RinvN_pos n |}).
                    move => H Eqball NH //.
                    move => NH Eqball NH'.
                    simpl in NH.
                    apply False_ind; apply NH => //.
                case_eq (ball_norm_dec zero (f x)  {|
                    RIneq.pos := / (INR n + 1);
                    RIneq.cond_pos := RiemannInt.RinvN_pos n |}).
                    move => H Eqball.
                    unfold whichn in Hwhichn.
                    rewrite Eqball in Hwhichn.
                    lia.
                move => NH Eqball.
                unfold whichn in Hwhichn.
                rewrite Eqball in Hwhichn.
                move: Hwhichn => /(whichn'_spec_lt_n _ _ Ltjn)//.

                unfold whichn.
                move => [Nball /(whichn'_spec_lt_n _ _ Ltjn) ->].
                case: (ball_norm_dec zero (f x) {|
                    RIneq.pos := / (INR n + 1);
                    RIneq.cond_pos := RiemannInt.RinvN_pos n |}) => //.
        Qed.

        Lemma whichn_spec_eq_n (n : nat) :
            ∀ x : X,
            whichn n x = n <-> ((¬ ∃ m : nat, (m < n)%nat ∧ A m (f x)) ∨ (ball_norm zero (/(INR n + 1)) (f x))).
        Proof.
            move => x; split.
                unfold whichn.
                case: (ball_norm_dec zero (f x)
                    {|
                    RIneq.pos := / (INR n + 1);
                    RIneq.cond_pos := RiemannInt.RinvN_pos n |}) => /=.
                move => ball_zero; right => //.
                move => _ /(whichn'_spec_eq_n) Hwhichn; left => //.
                case.
                move => /(whichn'_spec_eq_n).
                1, 2 : unfold whichn; case: (ball_norm_dec zero (f x)
                    {|
                    RIneq.pos := / (INR n + 1);
                    RIneq.cond_pos := RiemannInt.RinvN_pos n |}) => //.
        Qed.

    End construction_of_seq.

    (*
    Definition Bif_adapted_seq : 
        (fun_separable u (inRange f) φ) -> (measurable_fun gen open f)
        -> (is_finite (LInt_p μ (‖f‖)%fn))
            -> (nat -> simpl_fun E μ).
    (* Definition *)
        move => Hsep Hmeasurable Hintegrable n.
        induction n.
            (* cas initial : la fonction nulle *)
            pose which0 := fun (_ : X) => O.
            pose val0 := fun (_ : nat) => (zero : E).
            pose max_which0 := O.
            apply (mk_simpl_fun which0 val0 max_which0) => //.
                move => n Hn; unfold which0; apply measurable_Prop.
                lia.
            (* induction *)
            case: IHn => whichn valn max_whichn axn1 axn2 axn3 axn4.
            assert (0 < (/ (INR max_whichn + 1)))
                by apply RiemannInt.RinvN_pos.
            pose ɛ := RIneq.mkposreal (/ (INR max_whichn + 1)) H.
            assert (∀ x : X, inRange f (f x)) as IRff.
                move => x; exists x => //.
            pose k := (fun x : X => φ (f x) (IRff x) ɛ).
            pose (max_whichSn := S max_whichn).
            pose 
                (
                    valSn := fun (j : nat) =>
                        if j <=? max_whichn then u j else zero
                ).
            pose 
                (
                    whichSn := fun (x : X) =>
                        match RIneq.Rle_dec (‖f x‖) (/ (INR max_whichn + 1)) with
                            | left _ => max_whichSn
                            | right _ =>
                                if (k x) <=? max_whichSn then
                                    (k x)
                                else whichn x
                        end
                ).
            apply (mk_simpl_fun whichSn valSn max_whichSn).
                unfold valSn, max_whichSn.
                assert ((S max_whichn <=? max_whichn) = false) as R.
                    rewrite Nat.leb_gt => //.
                rewrite R; clear R => //.
                move => x; unfold max_whichSn, whichSn.
                case (RIneq.Rle_dec (‖ f x ‖) (/ (INR max_whichn + 1))) => //.
                    move => _; case_eq (k x <=? max_whichSn) => //.
                    move /Nat.leb_le => //.
                    move => _; constructor 2; apply axn2.
                move => j Hj.
                unfold whichSn.

    Definition prop_Bif_adapted_seq_aux :
        (fun_separable u (inRange f) φ) ->
            { s : nat -> simpl_fun E μ
                | (∀ x : X, is_lim_seq (fun n => s n x) (f x))
                ∧ (∀ n : nat, ∀ x : X, ‖ s n x ‖ <= 2 * ‖ f x ‖)
            }.
    (* Definition *)
    case => inRangefu Hdense.
    apply 
    *)

End Bif_adapted_seq.