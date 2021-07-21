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
.
    
Require Import
    hierarchy_notations
    simpl_fun
    BInt_sf
    Bsf_Lsf
    CUS_Lim_seq
    topology_compl
    series
    Bi_fun
    BInt_Bif
.

Require Import
    measure
    LInt_p
    Rbar_compl
    simple_fun
    measurable_fun
    sigma_algebra
    sigma_algebra_R_Rbar_new
.

(*

Section ae_eq_prop.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope Bif_scope.

    Lemma BInt_ae_zero {bf : Bif E μ} :
        ae_eq μ bf (fun _ => zero) ->
            BInt bf = zero.
    Proof.
        pose NZ := (fun x => bf x ≠ zero).
        assert (measurable gen NZ) as π.
        apply (measurable_Bif bf (fun x => x ≠ zero)).
        apply measurable_gen.
        apply NM_open_neq.
        unfold ae_eq, ae_rel.
        move => Hae0.
        apply: norm_eq_zero.
        suff: ((‖ BInt bf ‖)%hy <= 0).
        move => Le.
        apply RIneq.Rle_le_eq.
        split => //.
        apply norm_ge_0.
        apply RIneq.Rle_trans with (BInt (‖bf‖)).
        apply norm_BInt_le.
        assert (μ (λ x : X, bf x ≠ zero) = Finite 0%R) as negNZ.
        case Hae0 => A [Hle [HMA HμA]].
        suff: (Rbar_le (μ (λ x : X, bf x ≠ zero)) 0).
            move => HLe.
            apply Rbar_le_antisym => //.
            apply meas_ge_0.
            apply Rbar_le_trans with (μ A).
            apply measure_le => //.
            rewrite HμA; apply Rbar_le_refl.
        assert (is_finite (μ (λ x : X, bf x ≠ zero))) as π'.
        rewrite negNZ => //.
        apply RIneq.Rle_trans with
            (BInt (Bif_integrable_sf ι (integrable_sf_indic π π')) = μ P).

    Lemma BInt_ae_eq {bf bf' : Bif E μ} :
        ae_eq μ bf bf' -> BInt bf = BInt bf'.
    Proof.
        move => H.
        suff: (BInt (bf + (opp one) ⋅ bf') = zero).
        rewrite BInt_plus BInt_scal.
        move => Hzero.
        apply plus_reg_r with (opp one ⋅ (BInt bf'))%hy.
        rewrite Hzero.
        rewrite <-BInt_scal, <-BInt_plus.
        rewrite BInt_zero => //.
        move => x.
        rewrite Bif_fn_plus Bif_fn_scal.
        rewrite scal_opp_one plus_opp_r => //.
        apply: norm_eq_zero.
        suff: ((‖ BInt (bf + opp one ⋅ bf')%Bif ‖)%hy <= 0).
        move => Le.
        assert (0 <= (‖ BInt (bf + opp one ⋅ bf')%Bif ‖)%hy) as Ge.
        apply norm_ge_0.
        apply RIneq.Rle_le_eq => //.
        apply RIneq.Rle_trans with (BInt (‖ bf + opp one ⋅ bf' ‖)%Bif).
        apply norm_BInt_le.
        suff: (BInt (‖ bf + opp one ⋅ bf' ‖) = 0).
        move => ->; apply RIneq.Rle_refl.
        admit.
        (* la j'ai besoin d'un pont entre BInt et LInt_p ! 
         (ça doit venir avec de la convergence dominée )*)

    Admitted.

End ae_eq_prop.

*)