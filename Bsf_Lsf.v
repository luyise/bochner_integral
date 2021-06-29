Add LoadPath "~/Documents/CoqNotGit/LInt/LInt_p" as MILC.

From Coq Require Import 
    ssreflect
    ssrsearch
    List
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

Lemma is_finite_sum_Rbar_map {T : Type} :
    ∀ l : list T, ∀ f : T -> Rbar,
        (∀ a : T, In a l -> is_finite (f a)) -> is_finite (sum_Rbar_map l f).
Proof.
    induction l.
        move => f _; unfold sum_Rbar_map => //.
        move => f Hl; unfold sum_Rbar_map => /=.
        replace (sum_Rbar_l (map f l)) with (sum_Rbar_map l f) 
            by unfold sum_Rbar_map => //.
        assert (∀ a : T, In a l -> is_finite (f a)) as HypIHl.
            move => b Hb.
            apply Hl; right => //.
        pose Hsum := IHl f HypIHl; clearbody Hsum; unfold is_finite in Hsum.
        assert (is_finite (f a)) as Ha.
            apply Hl; left => //.
        unfold is_finite in Ha.
        rewrite <-Ha, <-Hsum => //.
Qed.

(*

Lemma sum_Rbar_map_Rbar_plus_finite {T : Type} :
    ∀ l : list T, ∀ f g : T -> Rbar, 
        (∀ a : T, In a l -> is_finite (f a) ∧ is_finite (g a))
        -> sum_Rbar_map l (fun a => Rbar_plus (f a) (g a))
            = Rplus (sum_Rbar_map l f) (sum_Rbar_map l g).
Proof.
Admitted.

*)

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

    (*

    (* Une fonction qui parcours les valeurs prises par une simpl_fun R μ 
    et qui en fait une liste de valeur utiles *)
    Definition Bsf_to_Lsf_list_aux (sf : simpl_fun (R_NormedModule) μ) (n : nat) 
    : { l : list R | 
        (∀ x : X, sf.(which) x < n -> List.In (sf x) l) ∧ (NoDup l)
        ∧ ( match n with O => zero | S n' => sum_n (λ k : nat, (real (μ (nth_carrier sf k))) ⋅ val sf k) n' end
            = sum_Rbar_map l
            ( λ y : R, Rbar_mult y (μ (λ x : X, sf x = y ∧ sf.(which) x < n)) ) ) }.
    (* Definition *)
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqf; rewrite <-Eqf => /=.
        induction n.
            apply: (exist _ (nil)); split.
                lia.
                simpl => //.
                split; [apply NoDup_nil | easy].
            case_eq (n <=? maxf); swap 1 2.
                move /Nat.leb_gt.
                case_eq n. 
                    lia.
                    move => n' Eqn.
                    move => Gen'maxf.
                    case: IHn => l [Pl [NoDupl Psum]].
                    apply: (exist _ l); split.
                        move => x _.
                        assert (which sf x ≤ max_which sf) as Hyp by apply ax_which_max_which.
                        replace (max_which sf) with maxf in Hyp by rewrite Eqf => //.
                        assert (which sf x < n) by lia.
                        apply Pl => //.
                        split => //.
                        rewrite sum_Sn.
                        replace (μ (nth_carrier sf (S n'))) with (Finite 0%R).
                        rewrite scal_zero_l plus_zero_r.
                        rewrite Eqn in Psum.
                        rewrite Psum.
                        Print Implicit sum_Rbar_map_ext_f.
                        rewrite (sum_Rbar_map_ext_f _ _ (λ y : R, Rbar_mult y (μ (λ x : X, sf x = y ∧ which sf x < S (S n'))))) => //.
                        move => y Inyl; congr Rbar_mult.
                        apply measure_ext => x; split; case.
                            auto.
                            move => -> _; split => //.
                            assert (which sf x ≤ maxf).
                                rewrite Eqf => /=; apply axf2.
                                lia.
                            rewrite (measure_ext _ μ _ (fun _ => False)).
                            rewrite meas_False => //.
                            move => x; split => //.
                            unfold nth_carrier.
                            assert (which sf x < S n').
                            assert (which sf x ≤ maxf).
                                rewrite Eqf => /=; apply axf2.
                                lia.
                                lia.
            move => /Nat.leb_le Lenmaxf.
            case: IHn => l [Pl [NoDupl Psum]].
            case: (in_dec RIneq.Req_EM_T (vf n) l); swap 1 2.
                move => NIn_vfn.
                apply: (exist _ ((vf n)::l)); split.
                move => x /Peano.le_S_n Hx.
                case_eq (which sf x <? n).
                    move /Nat.ltb_lt => /=; right; apply Pl => //.
                    move /Nat.ltb_ge/(Nat.le_antisymm _ _ Hx) <-; left.
                    replace vf with (val sf) by rewrite Eqf => //.
                    reflexivity. 
                    split. 
                        apply NoDup_cons => //.
                        unfold sum_Rbar_map => /=.
                        replace (sum_Rbar_l
                                    (List.map
                                    (λ y : R, Rbar_mult y (μ (λ x : X, sf x = y ∧ which sf x < S n))) l))
                            with (sum_Rbar_map l (λ y : R, Rbar_mult y (μ (λ x : X, sf x = y ∧ which sf x < S n))))
                            at 1 by unfold sum_Rbar_map => //.
                        rewrite (sum_Rbar_map_ext_f l _ (fun y : R => Rbar_mult y (μ (λ x : X, sf x = y ∧ which sf x < n)))).
                        replace (sum_n (λ n0 : nat, (real (μ (nth_carrier sf n0))) ⋅ val sf n0) n) with
                            ( plus ((real (μ (nth_carrier sf n))) ⋅ (val sf n))
                                (match n with
                                | 0 => zero
                                | S n' => sum_n (λ n : nat, (real (μ (nth_carrier sf n))) ⋅ (val sf n)) n'
                                end)).
                        rewrite Psum.
                        rewrite [in RHS]Rbar_plus_real.
                        congr plus => //.
                        unfold scal => /=; unfold mult => /=.
                        case (RIneq.Req_EM_T (vf n) 0%R); swap 1 2.
                            move => Neq_vfn_0.
                            rewrite [in RHS]Rbar_mult_real.
                                2 : easy. 
                            rewrite [in RHS]Raxioms.Rmult_comm.
                            congr mult.
                            2 : rewrite Eqf => //.
                                rewrite (measure_ext _ μ _ (λ x : X, sf x = vf n ∧ which sf x < S n)) => //.
                                move => x; split.
                                unfold nth_carrier, fun_sf => ->.
                                rewrite Eqf => /=; auto.
                                case; unfold nth_carrier, fun_sf => Eq_sfx_vfn Le_wfx_n.
                                case (le_lt_or_eq (which sf x) n) => //.
                                apply le_S_n => //.
                                move /Pl; unfold fun_sf; rewrite Eq_sfx_vfn.
                                move /NIn_vfn => //.
                            apply Rbar_bounded_is_finite with 0%R (μ (fun x : X => sf x = vf n)).
                                apply meas_ge_0.
                                apply measure_le.
                                apply measurable_inter.
                                apply measurable_sf_preim.
                                apply measurable_ext with (fun x => which sf x ≤ n).
                                lia.
                                apply sf_measurable_preim_le.
                                rewrite Eqf => //.
                                apply measurable_sf_preim.
                                move => x [-> _] //.
                                easy.
                                apply finite_sf_preim_neq_0 => //.
                        
                        unfold nth_carrier; rewrite Eqf => /= => ->.
                        rewrite RIneq.Rmult_0_r Rbar_mult_0_l => //.
                        
                        case (RIneq.Req_EM_T (vf n) 0%R); swap 1 2.
                            move => Neq_vfn_0.
                            rewrite Rbar_mult_comm.
                            apply (is_finite_Rbar_mult_finite_real (μ (λ x : X, sf x = vf n ∧ which sf x < S n)) (vf n)).
                            apply Rbar_bounded_is_finite with (real 0%R) (μ (λ x : X, sf x = vf n)).
                                apply meas_ge_0.
                                apply measure_le.
                                apply measurable_inter.
                                apply measurable_sf_preim.
                                apply measurable_ext with (fun x => which sf x ≤ n).
                                lia.
                                apply sf_measurable_preim_le.
                                rewrite Eqf => //.
                                apply measurable_sf_preim.
                                move => x [-> _] //.
                                easy.
                                apply finite_sf_preim_neq_0 => //.

                            move => ->; rewrite Rbar_mult_0_l => //.

                apply is_finite_sum_Rbar_map => y _.
                rewrite Rbar_mult_comm.
                apply is_finite_Rbar_mult_finite_real.
                apply Rbar_bounded_is_finite with 0%R (μ (fun x : X => which sf x < n)).
                apply meas_ge_0.
                apply measure_le.
                apply measurable_inter.
                apply measurable_sf_preim.
                1, 2 : apply sf_measurable_preim_lt; rewrite Eqf => //.
                1, 2 : easy.
                apply is_finite_sf_preim_lt; rewrite Eqf => //.

                clear Lenmaxf Pl Psum NIn_vfn; case: n.
                    rewrite sum_O plus_zero_r => //.
                    move => n; rewrite sum_Sn plus_comm => //.

                move => y Inyl.
                congr Rbar_mult.
                apply measure_ext => x; split; swap 1 2.
                    case => H1 H2; split; [assumption | lia].
                    move => [Eq_sfx_y /le_S_n/le_lt_or_eq].
                    case => //.
                    move => Eq_wsfx_n; apply False_ind.
                    unfold fun_sf in Eq_sfx_y.
                    rewrite Eq_wsfx_n in Eq_sfx_y.
                    rewrite Eqf in Eq_sfx_y; simpl in Eq_sfx_y.
                    rewrite Eq_sfx_y in NIn_vfn => //.

                move => In_vfn.
                apply: (exist _ l); split.
                move => x /le_S_n/le_lt_or_eq; case.
                    apply Pl.
                    unfold fun_sf => ->; rewrite Eqf => //.

                split => //.
                rewrite (sum_Rbar_map_ext_f l _ (fun y : R => Rbar_plus (Rbar_mult y (μ (λ x : X, sf x = y ∧ which sf x < n))) (Rbar_mult y (μ (λ x : X, val sf n = y ∧ which sf x = n)))) ); swap 1 2.
                    move => y Inyl.
                    rewrite <-Rbar_mult_plus_distr_l.
                        2, 3 : apply meas_ge_0.
                    congr Rbar_mult.
                    rewrite <-measure_additivity.
                        2, 3 : apply measurable_inter.
                        2 : apply measurable_sf_preim.
                        2 : apply sf_measurable_preim_lt.
                        2 : rewrite Eqf => //.
                        2 : apply measurable_Prop.
                        2 : apply ax_measurable; rewrite Eqf => //.
                        2 : lia.
                    apply measure_ext => x; split.
                        move => [Eq_sfx_y /le_S_n/le_lt_or_eq].
                        case.
                            move => Hlt; left; easy.
                            move => Heq; right.
                            unfold fun_sf in Eq_sfx_y; rewrite Heq in Eq_sfx_y; easy.
                        case; case.
                            move => Eq_sfx_y Hlt; split. 
                            easy. 
                            lia.
                            move => Eq_sfx_y Heq; split.
                            unfold fun_sf; rewrite Heq; assumption.
                            lia.
                    rewrite sum_Rbar_map_Rbar_plus_finite.
                        all : swap 1 2.
                        move => y Inyl; split.
                        rewrite Rbar_mult_comm.
                        apply is_finite_Rbar_mult_finite_real.
                        apply Rbar_bounded_is_finite with 0%R (μ (λ x : X, which sf x < n)).
                        apply meas_ge_0.
                        2 : easy.
                        2 : apply is_finite_sf_preim_lt; rewrite Eqf => //.
                        apply measure_le.
                        apply measurable_inter.
                        apply measurable_sf_preim.
                        apply sf_measurable_preim_lt.
                        rewrite Eqf => //.
                        apply sf_measurable_preim_lt.
                        rewrite Eqf => //.
                        move => x; case => //.
                        case: (RIneq.Req_EM_T y 0%R).
                            move ->.
                            rewrite Rbar_mult_0_l => //.
                            move => Neq0y.
                            rewrite Rbar_mult_comm.
                            apply is_finite_Rbar_mult_finite_real.
                            case_eq (n =? maxf); swap 1 2.
                                move /Nat.eqb_neq => Neq.
                                apply Rbar_bounded_is_finite with 0%R (μ (λ x : X, which sf x = n)).
                                apply meas_ge_0.
                                2 : easy.
                                2 : apply ax_finite; rewrite Eqf => /=.
                                apply measure_le.
                                apply measurable_inter.
                                apply measurable_Prop.
                                1, 2 : apply ax_measurable; rewrite Eqf => //.
                                move => x; case => //.
                                case: (le_lt_or_eq n maxf Lenmaxf) => //.

                                move /Nat.eqb_eq ->.
                                rewrite (measure_ext _ _ _ (fun _ => False)).
                                rewrite meas_False => //.
                                move => x; split => //.
                                rewrite Eqf => /=; move => [Abs _].
                                rewrite axf1 in Abs; rewrite <-Abs in Neq0y => //.
                    setoid_rewrite <-Psum at 1.
                    replace (sum_n (λ n0 : nat, (real (μ (nth_carrier sf n0))) ⋅ val sf n0) n) with
                        ( plus ((real (μ (nth_carrier sf n))) ⋅ (val sf n))
                            (match n with
                            | 0 => zero
                            | S n' => sum_n (λ n : nat, (real (μ (nth_carrier sf n))) ⋅ (val sf n)) n'
                            end)); swap 1 2.   
                            clear Lenmaxf Pl Psum In_vfn; case: n.
                            rewrite sum_O plus_zero_r => //.
                            move => n; rewrite sum_Sn plus_comm => //.
                    rewrite plus_comm; congr plus.
                    unfold nth_carrier.
                    unfold scal => /=; unfold mult => /=; rewrite Raxioms.Rmult_comm.

    *)

    (*
                
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

    *)

End Bochner_sf_Lebesgue_sf.
