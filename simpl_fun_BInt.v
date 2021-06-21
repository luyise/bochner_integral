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
.

Require Import 
    simpl_fun
    sum_list
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
    Context (μ : measure gen).

    Open Scope R_scope.
    Open Scope type_scope.
    Open Scope core_scope.

    Definition Rbar_to_R (x : Rbar) : R :=
        match x return R with
            | Finite y => y
            | p_infty | m_infty => 0
        end.

    (* Une définition un peu lourde mais calculable de l'intégrale de Boshner pour une fonction simple *)
    Definition BInt_sf (f : X -> E) (l : list ((X -> Prop) * E)) (π : simpl_fun_for μ l f) 
        : E :=
            sum_list (
                List.map
                    (fun (c : (X -> Prop) * E) => 
                        let (P, v) := c in
                        scal (Rbar_to_R (μ P)) v
                    )
                    l
            ).
    
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