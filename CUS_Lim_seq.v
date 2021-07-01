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