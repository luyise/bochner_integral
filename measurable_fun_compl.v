
From Coq Require Import
    ssreflect
    ssrsearch
    Lia

    Reals

    Utf8
.

From Coquelicot Require Import
    Hierarchy
    Continuity
.

Require Import
    sigma_algebra_R_Rbar_new
    measurable_fun
    simpl_fun
    sigma_algebra
    hierarchy_notations
.

Section US_measurable_gen2_open.

    Context {U : UniformSpace}.
    
    Lemma measurable_gen2_open_implies_open :
        ∀ P : U * U -> Prop,
        measurable (gen2 open open) P -> measurable open P.
    Proof.
        move => P.
        move => H; induction H.
        apply measurable_gen => x Ax.
        case: H => P1; case => P2 [HP1 [HP2 HA]].
        assert (open P1) as HP1'.
            case: HP1 => //.
            move => ->; apply open_true.
        assert (open P2) as HP2'.
            case: HP2 => //.
            move => ->; apply open_true.
        clear HP1 HP2.
        case_eq x => x1 x2 Eqx.
        move: Ax => /HA; move => [/HP1' Hlocx1 /HP2' Hlocx2].
        case: Hlocx1; move => [ɛ1 Hɛ1] Hlocx1.
        case: Hlocx2; move => [ɛ2 Hɛ2] Hlocx2.
        pose ɛ := Rmin ɛ1 ɛ2.
        assert (0 < ɛ)%R as Hɛ.
        apply: Rmin_Rgt_r; split => //.
        pose sigɛ := {| RIneq.pos := ɛ; RIneq.cond_pos := Hɛ |}.
        exists sigɛ; move => [y1 y2] Hxy.
        apply HA; split; apply [Hlocx1, Hlocx2].
        1, 2 : rewrite Eqx /=; case Hxy => /= [Hball1 Hball2].
        1, 2 : apply ball_le with ɛ.
        1, 3 : apply [Rmin_l, Rmin_r].
        1, 2 : assumption.
        
        apply measurable_empty.
        apply measurable_compl => //.
        apply measurable_union_countable => //.
    Qed.

End US_measurable_gen2_open.

Section NM_measurable_fun_op.

    Context {X : Set}.
    Context (gen : (X -> Prop) -> Prop).

    Context {A : AbsRing}.
    Context {E : NormedModule A}.

    Open Scope hy_scope.

    Lemma NM_measurable_fun_plus_op :
        measurable_fun open open (λ c : E * E, fst c + snd c).
    Proof.
        apply measurable_fun_continuous => x.
        apply continuous_plus.
        apply continuous_fst.
        apply continuous_snd.
    Qed.

End NM_measurable_fun_op.