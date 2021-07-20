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