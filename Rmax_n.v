From Coq Require Import
    ssreflect
    ssrsearch
    Utf8

    Lia

    Rdefinitions
    RIneq
    Rbasic_fun
.

From Coquelicot Require Import
    Hierarchy
    Rcomplements
.

Require Import
    hierarchy_notations
.

Section Rmax_n_def.

    Open Scope R_scope.

    Fixpoint Rmax_n (u : nat -> R) (n : nat) : R :=
        match n return R with
            | O => u O
            | S n' => Rmax (Rmax_n u n') (u n)
        end.

End Rmax_n_def.

Open Scope nat_scope.

Lemma le_lt_v_eq :
    ∀ k1 k2 : nat, k1 <= k2 ->
        k1 < k2 ∨ k1 = k2.
Proof. lia. Qed.

Close Scope nat_scope.

Section Rmax_n_prop.

    Open Scope R_scope.

    Lemma fo_le_Rmax_n (u : nat -> R) (n : nat) :
        ∀ k : nat, k ≤ n -> u k <= Rmax_n u n.
    Proof.
        induction n.
            (* n = O *)
            move => k Hk.
            assert (k = O) by lia; rewrite H; clear H.
            simpl; apply Rle_refl.
            (* n <> O *)
            move => k Hk => /=.
            case: (le_lt_v_eq k (S n)) => // Hk'.
                apply Rle_trans with (r2:=(Rmax_n u n)).
                    apply IHn; lia.
                    apply Rmax_l.
                rewrite Hk'.
                apply Rmax_r.
    Qed.

End Rmax_n_prop.