
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
        | approximation (s : nat -> simpl_fun E μ) :
            ∀ x : X, is_lim_seq (fun n => s n x) (f x)
            -> is_lim_seq' (fun n => LInt_p μ (‖ f - (s n) ‖)%fn) 0 -> BIF f.

End Boshner_integrable_fun.

Arguments BIF {X E gen} μ f.

(* On note L¹(X,μ,E) l'espace des fonction Boshner integrable de X vers E *)
Notation "'L¹(' X ',' μ ',' E ')'" := { f : X -> E | BIF μ f }
    (format "'[ ' 'L¹(' X ','  μ ','  E ')' ']'").

Section Bi_fun_prop.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    (*
    Theorem Cauchy_seq_approx :
        ∀ f : X -> E, ∀ s : nat -> simpl_fun E μ,
            is_lim_seq' (fun n => LInt_p μ (‖ f - (s n) ‖)%fn) 0 -> NM_Cauchy_seq (fun n => BInt_sf (s n)).
    Proof.
        move => f s Hs.
        unfold Cauchy_seq => ɛ Hɛ.
        unfold is_lim_seq' in Hs.
        Print RIneq.posreal.
        pose sighalfɛ := RIneq.mkposreal (ɛ * /2) (R_compl.Rmult_lt_pos_pos_pos _ _ (RIneq.Rgt_lt _ _ Hɛ) RIneq.pos_half_prf).
        case: (Hs sighalfɛ) => N /= HsN.
        exists N.
        move => p q Hp Hq.

    *)

End Bi_fun_prop.