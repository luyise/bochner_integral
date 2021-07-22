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

    Lemma BInt_Rplus {f g : X -> R} :
        ∀ bf : Bif μ f, ∀ bg : Bif μ g,
        BInt (bf + bg)%Bif = BInt bf + BInt bg.
    Proof.
        move => bf bg.
        rewrite BInt_plus => //.
    Qed.

    Lemma BInt_Rscal {f : X -> R} :
        ∀ bf : Bif μ f, ∀ a : R,
        BInt (a ⋅ bf)%Bif = a * BInt bf.
    Proof.
        move => bf a.
        rewrite BInt_scal => //.
    Qed.

    Lemma BInt_Ropp {f : X -> R} :
        ∀ bf : Bif μ f, ∀ a : R,
        BInt (- bf)%Bif = - BInt bf.
    Proof.
        move => bf a.
        rewrite BInt_opp => //.
    Qed.

    Lemma BInt_Rminus {f g : X -> R} :
        ∀ bf : Bif μ f, ∀ bg : Bif μ g,
        BInt (bf - bg)%Bif = BInt bf - BInt bg.
    Proof.
        move => bf bg.
        rewrite BInt_minus => //.
    Qed.

    Lemma BInt_Rlinearity {f g : X -> R} :
        ∀ bf : Bif μ f, ∀ bg : Bif μ g, ∀ a b : R,
            BInt (a ⋅ bf + b ⋅ bg)%Bif
            = (a * (BInt bf) + (b * (BInt bg))).
    Proof.
        move => bf bg a b.
        rewrite BInt_linearity => //.
    Qed.

    Lemma BInt_ge_0 {f : X -> R} :
        ∀ bf : Bif μ f,
        (∀ x : X, 0 <= f x) ->
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

    Lemma BInt_monotone {f g : X -> R} :
        ∀ bf : Bif μ f, ∀ bg : Bif μ g,
        (∀ x : X, f x <= g x) -> BInt bf <= BInt bg.
    Proof.
        move => bf bg Hle.
        suff: (0 <= (BInt bg)%Bif - (BInt bf)%Bif) by lra.
        rewrite <-BInt_Rminus.
        apply BInt_ge_0.
        move => x; unfold fun_plus, fun_scal.
        rewrite scal_opp_one.
        unfold plus => /=.
        unfold opp => /=.
        apply: Raux.Rle_0_minus => //.
    Qed.

End BInt_R_prop.