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

Section BInt_to_LInt_p.

    (* espace de départ *)
    Context {X : Set}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma BInt_LInt_p_eq :
        ∀ bf : Bif R_NormedModule μ,
        (∀ x : X, 0 <= bf x) ->
        BInt bf = LInt_p μ (bf : X -> R).
    Proof.
        case => f sf ι isf axfpw axfl1 /= axpos.
        apply lim_seq_eq => /=.
        apply (lim_seq_ext (fun n => real (LInt_p μ (fun x : X => sf n x)))).
        move => n.
        rewrite BInt_sf_LInt_SFp.
        rewrite <-LInt_p_SFp_eq => //.
        unfold sum_Rbar_nonneg.non_neg => x.
        simpl