Add LoadPath "~/Documents/CoqGit/completeModuleSummation" as CMS.

From Coq Require Import
    Utf8
    ssreflect

    Rdefinitions
    RIneq
.

From Coquelicot Require Import
    Hierarchy
.

From CMS Require Import
    series
.

Require Import
    hierarchy_notations
    simpl_fun
.

Open Scope nat_scope.
Open Scope R_scope.

(*
Dans cette première section, je reprend exactement le code de Coquelicot où
je retire les existentiels pour obtenir des preuves constructives.
*)

Section filterlim_complete_constr.

    Context {T : Type}.
    Context {U : CompleteSpace}.

    Lemma filterlim_locally_closely_correct :
        forall {F} {FF : ProperFilter F} (f : T -> U),
            filterlim (fun x => (f (fst x), f (snd x))) (filter_prod F F) closely ->
            filterlim f F (locally (lim (filtermap f F))).
    Proof.
        intros F FF f H.
        intros P [eps HP].
        refine (_ (complete_cauchy (filtermap f F) _ _ eps)).
        + now apply filter_imp.
        + apply cauchy_distance'.
        apply filter_le_trans with (2 := H).
        apply prod_filtermap_le.
    Qed.

    Lemma filterlim_locally_cauchy_correct :
        forall {F} {FF : ProperFilter F} (f : T -> U),
            (forall eps : posreal, exists P, F P /\ forall u v : T, P u -> P v -> ball (f u) eps (f v)) ->
            filterlim f F (locally (lim (filtermap f F))).
    Proof.
        intros F FF f H.
        apply (filterlim_locally_closely_correct f).
        apply filterlim_closely => //.
    Qed.

End filterlim_complete_constr.

Definition Cauchy_seq {S : UniformSpace} (u : nat -> S) : Prop :=
    ∀ ɛ : R, ɛ > 0 -> ∃ n : nat, ∀ p q : nat,
        p ≥ n -> q ≥ n -> ball (u p) ɛ (u q).

Section Cauchy_lim_seq_def.

    Context {S : CompleteSpace}.

    Definition lim_seq (u : nat -> S) :=
        lim (filtermap u eventually).
    
    Lemma filterlim_cauchy_seq_correct :
        ∀ u : nat → S,
            (∀ eps : posreal, ∃ P, eventually P ∧ ∀ p q : nat, P p → P q → ball (u p) eps (u q))
            -> filterlim u eventually (locally (lim_seq u)).
    Proof.
        move => u Hu.
        apply filterlim_locally_cauchy_correct => //.
    Qed.

    Lemma Cauchy_seq_eventually {u : nat -> S} :
        Cauchy_seq u -> (∀ eps : posreal, ∃ P, eventually P ∧ ∀ p q : nat, P p → P q → ball (u p) eps (u q)).
    Proof.
        unfold Cauchy_seq => Hu ɛ.
        case: ɛ => ɛ Pɛ.
        pose Pɛ' := Rlt_gt _ _ Pɛ; clearbody Pɛ'.
        case: (Hu ɛ Pɛ') => N HuN.
        exists (fun n => n ≥ N); split => //.
        exists N => //.
    Qed.
        
    Lemma is_filterlim_Cauchy_lim_seq :
        ∀ (u : nat -> S), Cauchy_seq u ->
            filterlim u eventually (locally (lim_seq u)).
    Proof.
        move => u /Cauchy_seq_eventually π.
        apply (filterlim_cauchy_seq_correct u π).
    Qed.
    
End Cauchy_lim_seq_def.

Section lim_seq_prop.

    Context {S : UniformSpace}.
    Context {T : UniformSpace}.

    Lemma lim_seq_cte :
        ∀ s : S,
        filterlim (fun _ : nat => s) eventually (locally s).
    Proof.
        move => s.
        apply filterlim_const.
    Qed.
    
    Lemma lim_seq_continuity :
        ∀ f : S -> T, ∀ s : S,
        filterlim f (locally s) (locally (f s))
            -> ∀ u : nat -> S,
            filterlim u eventually (locally s) -> filterlim (fun n => f (u n)) eventually (locally (f s)).
    Proof.
        move => f s Hf u Hu.
        apply filterlim_comp with (locally s) => //.
    Qed.

    Lemma lim_seq_pair :
        ∀ u : nat -> S, ∀ v : nat -> T, ∀ lu : S, ∀ lv : T,
            filterlim u eventually (locally lu) ->
            filterlim v eventually (locally lv) ->
            filterlim (fun n => (u n, v n)) eventually (filter_prod (locally lu) (locally lv)).
    Proof.
        move => u v lu lv Hu Hv.
        apply filterlim_pair => //.
    Qed.

End lim_seq_prop.

Definition NM_Cauchy_seq {A : AbsRing} {E : NormedModule A} (u : nat -> E) : Prop :=
    ∀ ɛ : R, ɛ > 0 -> ∃ n : nat, ∀ p q : nat,
        p ≥ n -> q ≥ n -> ball_norm (u p) ɛ (u q).

Section NM_Cauchy_lim_seq_def.

    Context {A : AbsRing}.
    Context {E : CompleteNormedModule A}.

    Lemma NM_Cauchy_seq_Cauchy_seq :
        ∀ u : nat -> E, NM_Cauchy_seq u -> Cauchy_seq u.
    Proof.
        move => u.
        unfold NM_Cauchy_seq, Cauchy_seq.
        move => Hnorm ɛ Hɛ.
        case: (Hnorm ɛ Hɛ).
        move => N Hn.
        exists N => p q Hp Hq.
        pose HnormNpq := Hn p q Hp Hq; clearbody HnormNpq.
        apply: norm_compat1 => //.
    Qed.
    
    Lemma NM_Cauchy_seq_lim_seq_correct :
    ∀ (u : nat -> E), ∀ (π : NM_Cauchy_seq u),
        is_lim_seq u (lim_seq u).
    Proof.
        move => u /NM_Cauchy_seq_Cauchy_seq π.
        apply: is_filterlim_Cauchy_lim_seq => //.
    Qed.

End NM_Cauchy_lim_seq_def.

Section NM_lim_seq_prop.

    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    Open Scope hy_scope.
    Open Scope fun_scope.

    Lemma lim_seq_plus :
        ∀ u v : nat -> E, ∀ lu lv : E,
            is_lim_seq u lu -> is_lim_seq v lv ->
                is_lim_seq (u + v) (lu + lv)%hy.
    Proof.
        move => u v lu lv Hu Hv.
        apply 
            (filterlim_comp 
                nat (E * E) E 
                (fun n : nat => (u n, v n)) (fun c : E * E => fst c + snd c)%hy
                eventually (filter_prod (locally lu) (locally lv)) (locally (lu + lv)%hy) 
            ).
        apply lim_seq_pair => //.
        apply filterlim_plus.
    Qed.

    Lemma lim_seq_scal :
        ∀ a : nat -> A, ∀ u : nat -> E, ∀ la : A, ∀ lu : E,
            is_lim_seq a la -> is_lim_seq u lu ->
                is_lim_seq (fun n : nat => (a n) ⋅ (u n))%hy (la ⋅ lu)%hy.
    Proof.
        move => a u la lu Ha Hu.
        apply 
            (filterlim_comp 
                nat (A * E) E 
                (fun n : nat => (a n, u n)) (fun c : A * E => (fst c) ⋅ (snd c))%hy
                eventually (filter_prod (locally la) (locally lu)) (locally (la ⋅ lu)%hy) 
            ).
        apply lim_seq_pair => //.
        apply filterlim_scal.
    Qed.

    Lemma lim_seq_scal_r :
        ∀ a : A, ∀ u : nat -> E, ∀ lu : E,
            is_lim_seq u lu ->
                is_lim_seq (a ⋅ u) (a ⋅ lu)%hy.
    Proof.
        move => a u lu Hu.
        apply (lim_seq_continuity (fun x : E => a ⋅ x)%hy) => //.
        apply filterlim_scal_r.
    Qed.

    Lemma lim_seq_scal_l :
        ∀ a : nat -> A, ∀ u : E, ∀ la : A,
            is_lim_seq a la ->
                is_lim_seq (fun n => a n ⋅ u)%hy (la ⋅ u)%hy.
    Proof.
        move => a u la Ha.
        apply (lim_seq_continuity (fun b : A => b ⋅ u)%hy) => //.
        apply filterlim_scal_l.
    Qed.

    Lemma lim_seq_opp :
        ∀ u : nat -> E, ∀ lu : E,
            is_lim_seq u lu ->
                is_lim_seq (fun n : nat => opp (u n)) (opp lu).
    Proof.
        move => u lu Hu.
        apply (lim_seq_continuity (fun x : E => opp x)) => //.
        apply filterlim_opp.
    Qed.
    
    Lemma lim_seq_mult :
        ∀ a b : nat -> A, ∀ la lb : A,
        is_lim_seq a la -> is_lim_seq b lb ->
            is_lim_seq (fun n => (a n) * (b n)) (la * lb)%hy.
    Proof.
        move => a b la lb Ha Hb.
        apply 
            (filterlim_comp 
                nat (A * A) A 
                (fun n : nat => (a n, b n)) (fun c : A * A => fst c * snd c)%hy
                eventually (filter_prod (locally la) (locally lb)) (locally (la * lb)%hy) 
            ).
        apply lim_seq_pair => //.
        apply filterlim_mult.
    Qed.

    Lemma lim_seq_norm :
        ∀ u : nat -> E, ∀ lu : E,
        is_lim_seq u lu -> is_lim_seq (‖ u ‖)%fn (‖ lu ‖)%hy.
    Proof.
        move => u lu Hu.
        apply (lim_seq_continuity (fun x : E => norm x)) => //.
        apply filterlim_norm.
    Qed.

    Lemma lim_seq_norm_zero :
        ∀ u : nat -> E,
        is_lim_seq (‖u‖)%fn 0 -> is_lim_seq u zero.
    Proof.
        move => u Hu.
        apply filterlim_norm_zero => //.
    Qed.

    Lemma lim_seq_bounded :
        ∀ u : nat -> E,
            (∃ lu : E, is_lim_seq u lu)
            -> { M : R | ∀ n : nat, (‖ u n ‖)%hy <= M }.
    Proof.
        move => u Hu.
        apply filterlim_bounded => //.
    Qed.

End NM_lim_seq_prop.