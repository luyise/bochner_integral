
Add LoadPath "~/Documents/CoqNotGit/LInt/LInt_p" as MILC.
Add LoadPath "~/Documents/CoqGit/completeModuleSummation" as CMS.

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
.

From CMS Require Import
    series
    complete_normed_module_series
.

From MILC Require Import
    measure
    LInt_p
    Rbar_compl
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
    Inductive BIF (f : X -> E) : Prop :=
        | approximation (seq : nat -> simpl_fun E μ) :
            ∀ x : X, is_lim_seq (fun n => seq n x) (f x)
            -> Lim_seq' (fun n => LInt_p μ (‖ f - (seq n) ‖)%fn) = 0 -> BIF f.

End Boshner_integrable_fun.

Arguments BIF {X E gen} μ f.

(* On note L¹(X,μ,E) l'espace des fonction Boshner integrable de X vers E *)
Notation "'L¹(' X ',' μ ',' E ')'" := { f : X -> E | BIF μ f }
    (format "'[ ' 'L¹(' X ','  μ ','  E ')' ']'").
