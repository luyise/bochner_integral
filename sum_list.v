From Coq Require Import 
    ssreflect
    ssrsearch
    Utf8

    List
.

From Coquelicot Require Import
    Hierarchy
.

Definition sum_list {G : AbelianGroup} : list G -> G :=
  fun l => fold_right plus zero l.