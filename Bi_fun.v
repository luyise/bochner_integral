
(*Add LoadPath "~/Documents/CoqNotGit/LInt/LInt_p" as MILC.*)
(* Add LoadPath ".." as MILC. *)
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

(*
From MILC Require Import 
    measure
    sigma_algebra    
.
*)

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
.

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
    Inductive BIF (f : X -> E) : Type :=
        | approximation (s : nat -> simpl_fun E μ) :
            (∀ x : X, is_lim_seq (fun n => s n x) (f x))
            -> is_LimSup_seq' (fun n => LInt_p μ (‖ f - (s n) ‖)%fn) 0 -> BIF f.

End Boshner_integrable_fun.

Arguments BIF {X E gen} μ f.

(* On note L¹(X,μ,E) l'espace des fonction Boshner integrable de X vers E *)
Notation "'L¹(' X ',' μ ',' E ')'" := { f : X -> E | BIF μ f }
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

        case: (is_SF_Bsf (‖ s n + (- s p)%sf ‖)%sf) => l Hl.
        apply measurable_fun_ext with (‖ s n - s p ‖)%sf.
        move => x; rewrite fun_sf_norm; unfold fun_norm;
            rewrite fun_sf_plus; unfold fun_plus => //.
        apply SF_aux_measurable_fun with l => //.
        
        (*
        apply: (measurable_fun_composition _ open).
        apply measurable_fun_ext with ((s n + (- s p)%sf))%sf.
            move => x.
            rewrite fun_sf_plus => //.
        apply (measurable_fun_sf (s n - s p)%sf).
        move => P. move /sigma_algebra_R_Rbar_new.measurable_R_equiv_oo.
        apply measurable_fun_continuous.
        apply filterlim_norm.
        *)

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

        case: (is_SF_Bsf (‖ s n + (- s q)%sf ‖)%sf) => l Hl.
        apply measurable_fun_ext with (‖ s n - s q ‖)%sf.
        move => x; rewrite fun_sf_norm; unfold fun_norm;
            rewrite fun_sf_plus; unfold fun_plus => //.
        apply SF_aux_measurable_fun with l => //.
        (*
        apply: (measurable_fun_composition _ open).
        apply measurable_fun_ext with ((s n + (- s q)%sf))%sf.
            move => x.
            rewrite fun_sf_plus => //.
        apply (measurable_fun_sf (s n - s q)%sf).
        move => P. move /sigma_algebra_R_Rbar_new.measurable_R_equiv_oo.
        apply measurable_fun_continuous.
        apply filterlim_norm.
        *)
    Qed.
        
End Bi_fun_prop.

Section BInt_BIF_def.

    (* espace de départ *)
    Context {X : Set}.
    Context (ι : inhabited X).
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {gen_im : (E -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Definition BInt_BIF (f : X -> E) (π : BIF μ f) :=
        match π return E with (approximation s Hspw Hsl1) =>
            lim_seq (fun n => BInt_sf (s n))
        end.

    Theorem is_lim_seq_BInt_BIF (f : X -> E) (π : BIF μ f) :
        match π return Prop with (approximation s Hspw Hsl1) =>
            is_lim_seq (fun n => BInt_sf (s n)) (BInt_BIF f π)
        end.
    Proof.
        case: π => s Hspw Hsl1.
        apply NM_Cauchy_seq_lim_seq_correct.
        apply Cauchy_seq_approx with f => //.
    Qed.

End BInt_BIF_def.