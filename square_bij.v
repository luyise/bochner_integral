From Coq Require Import
    ssreflect
    ssrsearch
    Arith
    Utf8
.

Section square_bij.

    Context (n : nat).

Definition square_bij :=
    fun c : (nat * nat) => 
    let (k1, k2) := c in
    k1 * n + k2.

Definition square_bij_inv :=
    fun m : nat =>
        ((m / n), (m mod n)).

Lemma is_bij_square :
    ∀ c : nat * nat, square_bij_inv (square_bij c) = c.
Admitted.

Lemma is_bij_square_inv :
    ∀ m : nat, square_bij (square_bij_inv m) = m.
Admitted.

Lemma confined_square_inv : ∀ n' : nat,
    ∀ m : nat, m < n * n' ->
        let (k1, k2) := square_bij_inv m in
        k1 < n ∧ k2 < n'.
Admitted.

Open Scope nat_scope.

Lemma confined_square : ∀ n' : nat,
    ∀ k1 k2 : nat,
        k1 < n ∧ k2 < n' -> square_bij (k1, k2) < (n * n').
Admitted.