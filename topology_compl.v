Add LoadPath "~/Documents/CoqGit/completeModuleSummation" as CMS.

From Coq Require Import
    ssreflect
    ssrsearch
    Utf8

    Reals
    RIneq
    Qreals
    Lra
.

From Coquelicot Require Import
    Hierarchy
.

Require Import
    CUS_Lim_seq
    countable_sets
    hierarchy_notations
.

Section open_subspaces.

    Context {S : UniformSpace}.

    (* I est un type d'indexation *)
    Lemma open_union {I : Type} :
        ∀ U : I -> (S -> Prop), (∀ i : I, open (U i))
            -> open (fun x => ∃ i : I, U i x).
    Proof.
        move => U HU x.
        case => i Uix.
        case: (HU i x). 
            exact Uix.
        move => ɛ Hɛ.
        exists ɛ => y Bxɛy.
        exists i; apply Hɛ => //.
    Qed.

    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    Open Scope hy_scope.

    Lemma NM_open_ball_norm : forall (a : E) (ɛ : R), 0 < ɛ -> open (ball_norm a ɛ).
    Proof.
        move => a ɛ Hɛ; unfold open => x Hx.
        suff: locally_norm x (ball_norm a ɛ)
            by apply locally_le_locally_norm.
        unfold locally_norm, ball_norm in Hx |- *.
        pose η := ɛ - (norm (minus x a)).
        assert (0 < η); unfold η.
        apply Rgt_lt, (Rgt_minus ɛ (norm (minus x a))) => //.
        pose sigη := mkposreal η H.
        exists sigη => y /= Hη.
        apply Rle_lt_trans with (norm (minus y x) + (norm (minus x a))).
        replace (minus y a) with (minus y x + minus x a)
            by rewrite <-(minus_trans x) => //.
        apply norm_triangle.
        clear sigη; clear H.
        replace ɛ with ((ɛ - ‖ minus x a ‖) + ‖ minus x a ‖) at 1.
        unfold plus => /=.
        apply (Rplus_lt_compat_r (‖ minus x a ‖) (‖ minus y x ‖) (ɛ - (‖ minus x a ‖))).
        unfold η in Hη.
        unfold plus => //.
        setoid_rewrite Rplus_assoc.
        rewrite Rplus_opp_l; apply Rplus_ne.
    Qed.

End open_subspaces.

Section closed_subspaces.

    Context {S : UniformSpace}.

    (* I est un type d'indexation *)
    (* Etonnament, je n'ai pas eu à utiliser de tier exclu ici ! *)
    Lemma closed_inter {I : Type} :
        ∀ F : I -> (S -> Prop), (∀ i : I, closed (F i))
            -> closed (fun x => ∀ i : I, F i x).
    Proof.
        move => F HF.
        move => x NHx i.
        unfold closed in HF.
        pose HFix := HF i x; clearbody HFix.
        apply HFix.
        move => H.
        apply NHx.
        unfold locally.
        unfold locally in H; case: H => ɛ Hɛ.
        exists ɛ => y /Hɛ => Abs.
        move => H'.
        apply Abs => //.
    Qed.

End closed_subspaces.

Section density.

    Context {S : UniformSpace}.

    (* Je définit ici une notion de densité fonctionnel :
    on se donne explicitement une fonction de choix permettant de savoir quel
    est l'élément proche dans la partie dense *)
    Definition fun_dense (P : S -> Prop) (Q : S -> Prop) (f : ∀ x : S, Q x -> posreal -> S) : Prop :=
        (∀ x : S, P x -> Q x) ∧
        (∀ x : S, ∀ π : Q x,
            ∀ ɛ : posreal, ball x ɛ (f x π ɛ) ∧ P (f x π ɛ)).

    Definition dense (P : S -> Prop) (Q : S -> Prop) : Prop :=
        ∃ f, fun_dense P Q f.

    Lemma fun_dense_dense {P Q : S -> Prop} {f : ∀ x : S, Q x -> posreal -> S} : 
        fun_dense P Q f -> dense P Q.
    Proof.
        exists f => //.
    Qed.

    Definition fun_separable (u : nat -> S) (P : S -> Prop) (f : ∀ x : S, P x -> posreal -> nat) : Prop :=
        (∀ n : nat, P (u n)) ∧
        (∀ x : S, ∀ π : P x,
            ∀ ɛ : posreal, ball x ɛ (u (f x π ɛ))).
    
    Definition separable (P : S -> Prop) : Prop :=
        ∃ u : nat -> S, ∀ x : S, P x ->
            ∀ ɛ : posreal, ∃ n : nat, ball x ɛ (u n).

    Lemma fun_separable_separable {u : nat -> S} {P : S -> Prop} {f : (∀ x : S, P x -> posreal -> nat)} :
        fun_separable u P f -> separable P.
    Proof.
        move => H; exists u => x Px ɛ.
        exists (f x Px ɛ); apply H.
    Qed.

End density.

Section denseQR.

    Definition QinR (x : R) :=
        ∃ r : Q, x = Q2R r.

    Definition denseQR_fn : ∀ x : R_UniformSpace, True -> posreal -> R_UniformSpace :=
        fun x _ sigɛ => Q2R 
            match sigɛ with mkposreal ɛ _ =>
                let q := up (/ɛ) in
                (Qmake (up (x*IZR q)) (Z.to_pos q))
            end.

    Theorem fun_denseQR : fun_dense QinR (fun _ : R_UniformSpace => True) denseQR_fn.
    Proof.
        split; [easy | unfold denseQR_fn; move => x _ [ɛ Hɛ]; split; swap 1 2].
        unfold QinR; exists ((up (x * IZR (up (/ ɛ))) # Z.to_pos (up (/ ɛ)))) => //.
        unfold ball => /=; unfold AbsRing_ball.
        pose a := x;
        pose b := (x + ɛ)%R;
        assert (ɛ = b - a)%R as Eqɛ. 
            unfold a, b;
            unfold Rminus;
            rewrite Rplus_assoc;
            replace (ɛ + - x)%R with (ɛ - x)%R by unfold Rminus => //;
            rewrite Rplus_minus => //.
        fold a.
        pose q := up (/ɛ).
        rewrite Eqɛ in q.
        rewrite Eqɛ; fold q.
        assert (a < b)%R.
            unfold a, b.
            replace x with (x + 0)%R at 1 
                by apply Rplus_ne.
            apply Rplus_lt_compat_l => //.
        unfold abs => /=.
        apply Raux.Rabs_lt.
        suff: (a < (Q2R (up (a * IZR q) # Z.to_pos q)) < b).
            case => H1 H2; split.
            rewrite Ropp_minus_distr.
            unfold minus => /=; unfold plus => /=; unfold opp => /=.
            lra.
            unfold minus, plus, opp => /=.
            lra.
        (* maintenant je peut reprendre telle quelle la preuve donnée dans topo_bases_R *)
        assert (0 < b-a)%R as T1.
        rewrite <-Eqɛ => //.
        assert (0 < /(b-a))%R as T2.
        now apply Rinv_0_lt_compat.
        assert (0 < IZR q)%R.
        now apply Rlt_trans with (2:=proj1 (archimed _)).
        unfold Q2R; simpl.
        rewrite Z2Pos.id.
        2: apply lt_IZR; easy.
        split.
        apply Rmult_lt_reg_r with (IZR q); try assumption.
        unfold Rdiv; rewrite Rmult_assoc Rinv_l.
        2: now apply Rgt_not_eq.
        rewrite Rmult_1_r.
        apply archimed.
        apply Rmult_lt_reg_r with (IZR q); try assumption.
        unfold Rdiv; rewrite Rmult_assoc Rinv_l.
        2: now apply Rgt_not_eq.
        rewrite Rmult_1_r.
        apply Rplus_lt_reg_r with (-(a*IZR q))%R.
        apply Rle_lt_trans with (1:=(proj2 (archimed _))).
        apply Rlt_le_trans with (IZR q * (b-a))%R;[idtac|right; ring].
        apply Rmult_lt_reg_r with (/(b-a))%R; try assumption.
        rewrite Rmult_assoc Rinv_r.
        2: now apply Rgt_not_eq.
        rewrite Rmult_1_l Rmult_1_r.
        apply archimed.
    Qed.

    Definition separableR_fn : ∀ x : R_UniformSpace, True -> posreal -> nat :=
        fun x π sigɛ => bij_QN
            match sigɛ with mkposreal ɛ _ =>
                let q := up (/ɛ) in
                (Qmake (up (x*IZR q)) (Z.to_pos q))
            end.

    Theorem fun_separableR : fun_separable (fun n => Q2R (bij_NQ n)) (fun _ => True) separableR_fn.
    Proof.
        split => //.
        unfold separableR_fn => x _ ɛ.
        case: fun_denseQR => [_ H].
        case: (H x I ɛ) => [{}H _].
        unfold denseQR_fn in H.
        rewrite bij_NQN => //.
    Qed.

    Theorem separableR : separable (fun _ : R_UniformSpace => True).
    Proof.
        exact (fun_separable_separable fun_separableR).
    Qed.

End denseQR.