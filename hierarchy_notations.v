(*
Je déclare ici un scope pour les notations usuelles pour plus
et scal dans les structures décrites par Coquelicot.Hierarchy
*)

From Coquelicot Require Import
    Hierarchy
.

Declare Scope hy_scope.
Delimit Scope hy_scope with hy.
Open Scope hy_scope.

Notation "a + b" := (plus a b) : hy_scope.

Notation "- a" := (opp a) : hy_scope.

Notation "a - b" := (plus a (- b))%hy : hy_scope.

Notation "a * b" := (mult a b) : hy_scope.

Notation "a ⋅ u" := (scal a u) (left associativity, at level 45) : hy_scope.

Notation "| u |" := (abs u) (at level 100) : hy_scope.

Notation "‖ u ‖" := (norm u) (at level 100) : hy_scope.

Notation "'∑' ( u ) n" := (sum_n u n) (at level 55) : hy_scope.

Notation "'∑' ( u ) n m" := (sum_n_m u n m) (at level 55) : hy_scope.