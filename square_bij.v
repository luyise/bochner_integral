From Coq Require Import
    ssreflect
    ssrsearch
    Arith
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
        ∀ c : nat * nat, square_bij_inv n (square_bij n c) = c.
    Admitted.

    Lemma is_bij_square_inv :
        ∀ m : nat, square_bij n (square_bij_inv n m) = m.
    Admitted.

    Lemma square_bij_corner :
        ∀ n' : nat,
            square_bij (S n) (n', n) = ((S n') * (S n) - 1).
    Admitted.

    Lemma square_bij_inv_corner :
        ∀ n' : nat,
            square_bij_inv (S n) ((S n') * (S n) - 1) = (n', n).
    Admitted.

    Lemma confined_square_inv : ∀ n' : nat,
        ∀ m : nat, m <= S n' * S n - 1 ->
            let (k1, k2) := square_bij_inv (S n) m in
            k1 <= n' ∧ k2 <= n.
    Admitted.

    Lemma confined_square : ∀ n' : nat,
        ∀ k1 k2 : nat,
            k1 <= n' ∧ k2 <= n -> square_bij (S n) (k1, k2) <= (S n' * S n) - 1.
    Admitted.

End square_bij_prop.

Global Opaque square_bij.
Global Opaque square_bij_inv.