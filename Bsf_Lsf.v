Add LoadPath "~/Documents/CoqNotGit/LInt/LInt_p" as MILC.

From Coq Require Import 
    ssreflect
    ssrsearch
    Lia
    Utf8

    ClassicalDescription
    Rdefinitions
    Rbasic_fun
    .

From Coquelicot Require Import
    Hierarchy
    Rbar
.

From MILC Require Import 
    measure
    sigma_algebra
    sum_Rbar_nonneg
    Rbar_compl
    simple_fun
.

Require Import 
    simpl_fun
    hierarchy_notations
    BInt_sf
.

Section Bochner_sf_Lebesgue_sf.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : R *)
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope nat_scope.
    Open Scope list_scope.

    Lemma le_zero {n : nat} : n ≤ O -> n = O.
    Proof. lia. Qed.

    (* Une fonction qui parcours les valeurs prises par une simpl_fun R μ 
    et qui en fait une liste de valeur utiles *)
    Definition Bsf_to_Lsf_list_aux (sf : simpl_fun (R_NormedModule) μ) (n : nat) 
    : { l : list R | 
        (∀ x : X, sf.(which) x < n -> List.In (sf x) l)
        ∧ ( match n with O => zero | S n' => sum_n (λ k : nat, (real (μ (nth_carrier sf k))) ⋅ val sf k) n' end
            = sum_Rbar_map l
            ( λ y : R, Rbar_mult y (μ (λ x : X, sf x = y ∧ sf.(which) x < n)) ) ) }.
    (* Definition *)
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqf; rewrite <-Eqf => /=.
        induction n.
            apply: (exist _ (nil)); split.
                lia.
                simpl => //.
                (*
                move ->; left => //.
                rewrite sum_O; unfold sum_Rbar_map => /=; rewrite Rbar_plus_0_r.
                rewrite Rbar_mult_comm; unfold scal => /=; unfold mult => /=.
                rewrite Rbar_mult_real.
                congr Rmult; unfold nth_carrier.
                assert (∀ x : X, which sf x = 0 <-> sf x = val sf 0 ∧ which sf x ≤ 0).
                    move => x; split.
                    unfold fun_sf; move => -> //.
                    move => [_ /le_zero] //.
                    rewrite (measure_ext _ _ _ _ H) => //.
                    assert (val sf 0 )
                *)
            case: IHn => l [Pl Psum].
            apply: (exist _ ((vf n)::l)); split.
            move => x /Peano.le_S_n Hx.
            case_eq (which sf x <? n).
                move /Nat.ltb_lt => /=; right; apply Pl => //.
                move /Nat.ltb_ge/(Nat.le_antisymm _ _ Hx) <-; left.
                replace vf with (val sf) by rewrite Eqf => //.
                reflexivity.
            unfold sum_Rbar_map => /=.
            replace (sum_Rbar_l
                        (List.map
                        (λ y : R, Rbar_mult y (μ (λ x : X, sf x = y ∧ which sf x < S n))) l))
                with (sum_Rbar_map l (λ y : R, Rbar_mult y (μ (λ x : X, sf x = y ∧ which sf x < S n))))
                at 1 by unfold sum_Rbar_map => //.
            replace (sum_n (λ n0 : nat, (real (μ (nth_carrier sf n0))) ⋅ val sf n0) n) with
                ( plus ((real (μ (nth_carrier sf n))) ⋅ (val sf n))
                    (match n with
                    | 0 => zero
                    | S n' => sum_n (λ n : nat, (real (μ (nth_carrier sf n))) ⋅ (val sf n)) n'
                    end)).
                rewrite Psum. unfold plus; simpl.
                rewrite [in RHS]Rbar_plus_real.
                congr plus => //.
    Defined.

    Definition Bsf_to_Lsf_list (sf : simpl_fun (R_NormedModule) μ)
    : { l : list R | finite_vals_canonic sf l }.
        case: (Bsf_to_Lsf_list_aux sf (S (max_which sf))) => l Pl.
        pose l_can := canonizer sf l; apply: (exist _ l_can).
        unfold l_can; apply finite_vals_canonizer => x.
        pose Hx := ax_which_max_which sf x; clearbody Hx.
        apply Pl, le_n_S => //.
    Defined.

    Definition is_SF_Bsf (sf : simpl_fun (R_NormedModule) μ) : SF gen sf.
    (* Definition *)
        case: (Bsf_to_Lsf_list sf) => l Hl.
        apply (exist _ l); split => //.
        move => y.  unfold fun_sf.
        pose A := fun n => (λ x : X, which sf x = n ∧ val sf n = y).
        assert (∀ n : nat, n ≤ max_which sf -> measurable gen (A n)).
            move => n Hn; apply measurable_inter.
                2 : apply measurable_Prop.
                apply ax_measurable => //.
            apply measurable_ext with (fun x => exists n, (n <= max_which sf)%nat /\ A n x).
                move => x; split.
                    case => n [Hn [-> Goal]] => //.
                    move => Hy.
                    exists (which sf x); split.
                        apply ax_which_max_which.
                        split => //.
        apply measurable_union_finite => //.
    Defined.

    Lemma BInt_sf_LInt_SFp :
        ∀ sf : simpl_fun R_NormedModule μ, BInt_sf sf = LInt_SFp μ sf (is_SF_Bsf sf).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqf; rewrite <-Eqf => /=.
        unfold BInt_sf, LInt_SFp.
        unfold af1.

End Bochner_sf_Lebesgue_sf.
