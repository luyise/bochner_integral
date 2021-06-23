From Coq Require Import
    ssreflect
    ssrsearch
    Arith
    Lia
    Utf8
.

Section square_bij_def.

    Context (n : nat).

    Definition square_bij :=
        fun c : (nat * nat) => 
        let (k1, k2) := c in
        k1 * n + k2.

    Definition square_bij_inv :=
        fun m : nat =>
            ((m / n), (m mod n)).

End square_bij_def.

Section square_bij_prop.

    Context (n : nat).

    Lemma is_bij_square :
        ∀ k1 k2 : nat, k2 <= n -> square_bij_inv (S n) (square_bij (S n) (k1, k2)) = (k1, k2).
    Proof.
        move => k1 k2 Hk2.
        unfold square_bij, square_bij_inv.
        congr pair.
            rewrite Nat.div_add_l => //.
            rewrite Nat.div_small => //.
            apply le_n_S => //.
            rewrite Nat.add_comm.
            rewrite Nat.mod_add => //.
            rewrite Nat.mod_small => //.
            apply le_n_S => //.
    Qed.

    Lemma confined_snd_square_inv :
        ∀ m : nat, (snd (square_bij_inv (S n) m)) <= n.
    Proof.
        move => m.
        unfold square_bij_inv, snd.
        suff: (m mod S n < S n) by lia.
        apply Nat.mod_upper_bound => //.
    Qed.

    Lemma is_bij_square_inv :
        ∀ m : nat, square_bij (S n) (square_bij_inv (S n) m) = m.
    Proof.
        move => m; unfold square_bij_inv, square_bij.
        rewrite Nat.mul_comm.
        rewrite <-Nat.div_mod => //.
    Qed.

    Lemma square_bij_corner :
        ∀ n' : nat,
            square_bij (S n) (n', n) = ((S n') * (S n) - 1).
    Proof.
        unfold square_bij; lia.
    Qed.

    Lemma square_bij_inv_corner :
        ∀ n' : nat,
            square_bij_inv (S n) ((S n') * (S n) - 1) = (n', n).
    Proof.
        move => n'.
        pose Hnn' := square_bij_corner n'; clearbody Hnn'.
        assert 
            (square_bij_inv (S n) (square_bij (S n) (n', n))
            = square_bij_inv (S n) (S n' * S n - 1))
            as Eq by congruence.
        rewrite is_bij_square in Eq; easy.
    Qed.

    Lemma confined_square_inv : ∀ n' : nat,
        ∀ m : nat, m <= S n' * S n - 1 ->
            let (k1, k2) := square_bij_inv (S n) m in
            k1 <= n' ∧ k2 <= n.
    Proof.
        move => n' m Hm; split.
        assert (m < S n' * S n) by lia.
        suff: (m / S n < S n') by lia.
        apply Nat.div_lt_upper_bound => //.
            rewrite Nat.mul_comm => //.
        suff: (m mod S n < S n) by lia.
        apply Nat.mod_upper_bound => //.
    Qed.

    Lemma confined_square : ∀ n' : nat,
        ∀ k1 k2 : nat,
            k1 <= n' ∧ k2 <= n -> square_bij (S n) (k1, k2) <= (S n' * S n) - 1.
    Proof.
        move => n' k1 k2 [Hk1 Hk2].
        unfold square_bij.
        replace 
            (S n' * S n - 1)
            with
            ((n' * S n) + n)
            by lia.
        apply plus_le_compat => //.
        apply mult_le_compat => //.
    Qed.

End square_bij_prop.

Global Opaque square_bij.
Global Opaque square_bij_inv.