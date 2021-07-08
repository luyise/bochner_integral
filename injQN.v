Require Import
  QArith
  Utf8
  ssreflect
.

Definition Q2N : Q -> nat.
Admitted.
Definition N2Q : nat -> Q.
Admitted.

Lemma Q2N2Q : ∀ r : Q, N2Q (Q2N r) = r.
Admitted.