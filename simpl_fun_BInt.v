Add LoadPath "~/Documents/CoqNotGit/LInt/LInt_p" as MILC.

From Coq Require Import 
    ssreflect
    ssrsearch
    Utf8

    Rdefinitions
.

From Coquelicot Require Import
    Hierarchy
    Rbar
.

From MILC Require Import 
    measure
    sigma_algebra
.

Require Import 
    simpl_fun
.

Section BInt_for_sf.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope R_scope.

    (* Une définition un peu lourde mais calculable de l'intégrale de Boshner pour une fonction simple *)
    Definition BInt_sf (sf : @simpl_fun _ _ E _ μ) : E :=
        sum_n
            (fun n => scal (real (μ (nth_carrier sf n))) (sf.(val) n))
            (sf.(max_which)).
    
    Notation "'∫B' sf 'd' μ" := (BInt_sf (sf : @simpl_fun _ _ E _ μ)) (at level 10).

    (*
    Lemma BInt_sf_indep_of_dec :
        ∀ f : X -> E, ∀ l l' : list ((X -> Prop) * E),
        ∀ π : simpl_fun_for μ l f, ∀ π' : simpl_fun_for μ l' f,
        BInt_sf f l π = BInt_sf f l' π'.
    *)
    (* Idées pour s'y prendre avec ce lemme :
        1. s'en sortir avec un lemme d'extensionnalité (violent)
            ça doit être faisable avec la définition des fonctions simples
        2. commencer par montrer que cette définition est un morphisme pour +
            et remarquer que f - f admet une décomposition triviale donnant une intégrale nulle 
    *)

End BInt_for_sf.

Section Bint_sf_plus.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope R_scope.
    Open Scope nat_scope.

    (*
    Lemma BInt_sf_plus_aux :
        ∀ sf_f sf_g : @simpl_fun _ _ E _ μ,
            BInt_sf (simpl_fun_plus_aux sf_f sf_g) = plus (BInt_sf sf_f) (BInt_sf sf_g).
    Proof.
        move => sf_f sf_g.
        case_eq sf_f => wf vf maxf axf1 axf2 axf3 axf4 Eqf.
        case_eq sf_g => wg vg maxg axg1 axg2 axg3 axg4 Eqg.
        rewrite <-Eqf, <- Eqg.
        unfold BInt_sf.
        replace (max_which sf_f) with maxf by rewrite Eqf => //.
        replace (max_which sf_g) with maxg by rewrite Eqg => //.
        replace (max_which (simpl_fun_plus_aux sf_f sf_g)) with ((S maxf) * (S maxg) - 1).
            2 : rewrite Eqf Eqg => //.
        unfold nth_carrier.
    Abort.
    *)


End Bint_sf_plus.