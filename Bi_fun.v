
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
  forall u : nat -> Rbar, forall a : R, forall l : R,
    is_LimSup_seq' (fun n => Rbar_mult a (u n)) (Rbar_mult a l).
Admitted.

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
    Context (π : inhabited X).
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma Cauchy_seq_approx :
        ∀ f : X -> E, ∀ s : nat -> simpl_fun E μ,
            (∀ x : X, is_lim_seq (fun n => s n x) (f x)) -> is_LimSup_seq' (fun n => LInt_p μ (‖ f - (s n) ‖)%fn) 0 
            -> NM_Cauchy_seq (fun n => BInt_sf (s n)).
    Proof.
        move => f s Hspointwise Hs.
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
            2 : exact π.
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
            2 : exact π.
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
            2 : exact π.
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
    Context (ι : inhabited X).
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.
    Context {f g : X -> E}.

    Definition Bif_plus (bf : Bif μ f) (bg : Bif μ g) : Bif μ (f + g)%fn.
        case: bf => sf Hfpw Hfl1;
        case: bg => sg Hgpw Hgl1.
        apply: (approximation (f + g)%fn (fun n : nat => sf n + sg n)%sf).
            move => x; unfold fun_plus.
            apply (lim_seq_ext (fun n => sf n x + sg n x)%hy).
                move => n; rewrite fun_sf_plus => //.
            apply: lim_seq_plus => //.

        unfold is_LimSup_seq' => ɛ; split; swap 1 2.
        simpl; rewrite Raxioms.Rplus_0_l.

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
        
        case: ɛ => [ɛ Hɛ].
        pose sighalfɛ := RIneq.mkposreal (ɛ * /2) (R_compl.Rmult_lt_pos_pos_pos _ _ (RIneq.Rgt_lt _ _ Hɛ) RIneq.pos_half_prf).
        case: (Hfl1 sighalfɛ) => [HfMaj {}Hf].
        case: (Hgl1 sighalfɛ) => [HgMaj {}Hg].
        case: Hf => N HfN.
        case: Hg => N' HgN'.
        exists (max N N').
        move => n Hn => /=.
        unfold minus.

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
        
        apply: (measurable_fun_composition _ open).
        apply measurable_fun_ext with ((sf k + (- sf n)%sf))%sf.
            move => x.
            rewrite fun_sf_plus => //.
        apply (measurable_fun_sf (sf k - sf n)%sf).
        move => P; move /sigma_algebra_R_Rbar_new.measurable_R_equiv_oo.
        apply measurable_fun_continuous.
        apply filterlim_norm.

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
        case_eq bf => sf Hfpw Hfl1 Eqf.
        apply: (approximation (a ⋅ f)%fn (fun n : nat => a ⋅ sf n)%sf).
            move => x; unfold fun_scal.
            apply (lim_seq_ext (fun n => a ⋅ sf n x)%hy).
                move => n; rewrite fun_sf_scal => //.
            apply: lim_seq_scal_r => //.

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
            
            apply: (measurable_fun_composition _ open).
            apply measurable_fun_ext with ((sf k + (- sf n)%sf))%sf.
                move => x.
                rewrite fun_sf_plus => //.
            apply (measurable_fun_sf (sf k - sf n)%sf).
            move => P; move /sigma_algebra_R_Rbar_new.measurable_R_equiv_oo.
            apply measurable_fun_continuous.
            apply filterlim_norm.

            assert (Rbar_mult (|a|)%hy 0 = 0).
            unfold Rbar_mult => /=.
            rewrite RIneq.Rmult_0_r => //.

            rewrite <-H.
            apply is_LimSup_seq'_scal_l.
        
    Qed.

End Bif_op.

(*
Notation "bf + bg" := (Bif_plus ι bf bg) : Bif_scope.
*)