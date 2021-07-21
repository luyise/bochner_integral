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
    BInt_LInt_p
.

Section BInt_R_prop.

    Context {X : Set}.
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma BInt_Rplus :
        ∀ bf bg : Bif R_NormedModule μ,
        BInt (bf + bg)%Bif = BInt bf + BInt bg.
    Proof.
        move => bf bg.
        rewrite BInt_plus => //.
    Qed.

    Lemma BInt_Rscal :
        ∀ bf : Bif R_NormedModule μ, ∀ a : R,
        BInt (a ⋅ bf)%Bif = a * BInt bf.
    Proof.
        move => bf a.
        rewrite BInt_scal => //.
    Qed.

    Lemma BInt_Ropp :
        ∀ bf : Bif R_NormedModule μ, ∀ a : R,
        BInt (- bf)%Bif = - BInt bf.
    Proof.
        move => bf a.
        rewrite BInt_opp => //.
    Qed.

    Lemma BInt_Rminus :
        ∀ bf bg : Bif R_NormedModule μ,
        BInt (bf - bg)%Bif = BInt bf - BInt bg.
    Proof.
        move => bf bg.
        rewrite BInt_minus => //.
    Qed.

    Lemma BInt_Rlinearity :
        ∀ (bf bg : Bif R_NormedModule μ), ∀ a b : R,
            BInt (a ⋅ bf + b ⋅ bg)%Bif
            = (a * (BInt bf) + (b * (BInt bg))).
    Proof.
        move => bf bg a b.
        rewrite BInt_linearity => //.
    Qed.

    Lemma BInt_ge_0 :
        ∀ bf : Bif R_NormedModule μ,
        (∀ x : X, 0 <= bf x) ->
            0 <= BInt bf.
    Proof.
        move => bf H.
        rewrite BInt_LInt_p_eq => //.
        suff: Rbar_le 0 (LInt_p μ (λ x : X, bf x)).
        rewrite <-is_finite_LInt_p_Bif => //.
        apply LInt_p_ge_0.
        exact (ax_notempty bf).
        move => x //=.
    Qed.

    Lemma BInt_monotone :
        ∀ bf bg : Bif R_NormedModule μ,
        (∀ x : X, bf x <= bg x) -> BInt bf <= BInt bg.
    Proof.
        move => bf bg Hle.
        suff: (0 <= (BInt bg)%Bif - (BInt bf)%Bif) by lra.
        rewrite <-BInt_Rminus.
        apply BInt_ge_0.
        move => x; rewrite Bif_fn_plus Bif_fn_scal.
        rewrite scal_opp_one.
        unfold plus => /=.
        unfold opp => /=.
        apply: Raux.Rle_0_minus => //.
    Qed.

End BInt_R_prop.