
(* Add LoadPath "~/Documents/CoqNotGit/LInt/LInt_p" as MILC. *)
(* Add LoadPath ".." as MILC. *)

From Coq Require Import 
    ssreflect
    ssrsearch
    Arith
    Lia
    Utf8

    ClassicalDescription

    Rdefinitions
.

From Coquelicot Require Import
    Hierarchy
    Rbar
.

Require Import 
    measure
    sigma_algebra
    sum_Rbar_nonneg
    Rbar_compl
    measurable_fun
.

Require Import
    square_bij
    hierarchy_notations
    Rmax_n
.

Declare Scope sf_scope.
Delimit Scope sf_scope with sf.

Declare Scope fun_scope.
Delimit Scope fun_scope with fn.

Open Scope hy_scope.
Open Scope fun_scope.
Open Scope sf_scope.

Section simpl_fun_def.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : ModuleSpace A}.

    Definition indic (P : X -> Prop) : X -> A :=
        fun x =>
            match (excluded_middle_informative (P x)) return A with
                | left _ => one
                | right _ => zero
            end.

    Open Scope core_scope.
    Open Scope type_scope.
    Open Scope nat_scope.
    
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}. 
    Context {μ : measure gen}.

    (* la fonction est val ∘ which *)
    Record simpl_fun := mk_simpl_fun {
        which : X -> nat;
        val : nat -> E;
        max_which : nat;

        ax_val_max_which :
            val max_which = zero;
        ax_which_max_which :
            ∀ x : X, which x <= max_which;
        ax_measurable :
            ∀ n : nat, n <= max_which ->
                measurable gen (fun x => which x = n);
        ax_finite :
            ∀ n : nat, n < max_which ->
                is_finite (μ (fun x => which x = n))
    }.

    Definition meas_of_sf (sf : simpl_fun) := μ.

    Definition nth_carrier (sf : simpl_fun) (n : nat) : (X -> Prop) :=
        (fun x => sf.(which) x = n).

    Definition fun_sf (sf : simpl_fun) : X -> E :=
        fun x => sf.(val) (sf.(which) x).

    (* On se donne la possibilité de calculer la "valeur" d'une simpl_fun en l'évaluant en x : *)
    Coercion fun_sf : simpl_fun >-> Funclass.

    (* Un exemple d'utilisation est fait dans cete définition *)
    Definition is_simpl (f : X -> E) :=
        ∃ sf : simpl_fun, ∀ x : X, sf x = f x.

End simpl_fun_def.

Arguments simpl_fun {X A} E {gen} μ.
Arguments is_simpl {X A} [E] {gen} μ f.

Notation "'χ(' P ')'" := (indic P) (at level 0) : fun_scope.

Section simpl_fun_indic.

    (* espace de départ *)
    Context  {X : Set}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context (μ : measure gen).

    Open Scope nat_scope.
    Open Scope R_scope.

    Definition sf_indic_aux (P : X -> Prop) :
        measurable gen P -> is_finite (μ P) -> simpl_fun R_ModuleSpace μ.
    (* définition *)
        move => Pmeas Pfin.
        pose w := fun x =>
            match (excluded_middle_informative (P x)) return nat with
                | left _ => O
                | right _ => (S O)
            end.
        pose v := fun n =>
            match n return R with
                | O => 1
                | _ => 0
            end.
        pose max_w := (S O).
        apply (mk_simpl_fun w v max_w).
            unfold max_w => //.
            move => x; unfold w, max_w.
            case: (excluded_middle_informative (P x)); lia.
            unfold max_w; case.
                move => _.
                apply measurable_ext with P.
                unfold w => x.
                case: (excluded_middle_informative (P x)) => //.
                exact Pmeas.
            move => n Hn.
            assert (S n = 1%nat) by lia.
            rewrite H; clear Hn H; clear n.
            apply measurable_ext with (fun x => ¬ P x).
            unfold w => x.
            case: (excluded_middle_informative (P x)) => //.
            apply measurable_compl.
            apply measurable_ext with (fun x => P x).
            move => x; split; case: (excluded_middle_informative (P x)).
                move => _; auto.
                auto.
                auto.
                move => NPx NNPx; apply False_ind.
                exact (NNPx NPx).
            exact Pmeas.
            move => n Hn.
            assert (n = O) by lia.
            rewrite H; clear H Hn; clear n.
            rewrite <-(measure_ext gen _ P).
            exact Pfin.
            move => x; unfold w.
                case (excluded_middle_informative (P x)) => //.
    Defined.

    Lemma sf_indic :
        ∀ P : X -> Prop, measurable gen P -> is_finite (μ P)
            -> is_simpl μ (χ(P): X -> R).
    Proof.
        move => P Pmeas Pfin.
        exists (sf_indic_aux P Pmeas Pfin) => x.
        unfold fun_sf, "χ( _ )" => /=.
        case: (excluded_middle_informative (P x)) => //.
    Qed.

End simpl_fun_indic.

Section simpl_fun_norm.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope R_scope.
    Open Scope nat_scope.

    Definition fun_norm (f : X -> E) :=
        fun x => norm (f x).

    Notation "‖ f ‖" := (fun_norm f) (at level 100) : fun_scope.

    Definition sf_norm_aux (sf : simpl_fun E μ) : simpl_fun R_ModuleSpace μ.
        case: sf => which val max_which ax1 ax2 ax3 ax4.
        pose nval :=
            fun n => norm (val n).
        apply (mk_simpl_fun which nval max_which).
            (* ax_val_max_which *)
            unfold nval; rewrite ax1.
            apply norm_zero; assumption.
            (* ax_which_max_which *)
            exact ax2.
            (* ax_measurable *)
            exact ax3.
            (* ax_finite *)
            exact ax4.
    Defined.

    Notation "‖ sf ‖" := (sf_norm_aux sf) (at level 100) : sf_scope.

    Lemma sf_norm :
        ∀ f : X -> E, is_simpl μ f -> 
            is_simpl μ (fun_norm f).
    Proof.
        move => f.
        case => sf. case_eq sf => which val max_which ax1 ax2 ax3 ax4 Eqsf Eqf.
        exists (sf_norm_aux sf).
        rewrite Eqsf.
        move => x; unfold fun_sf, sf_norm_aux => /=.
        simpl in Eqf.
        rewrite Eqf => //.
    Qed.

    Lemma fun_sf_norm :
        ∀ sf : simpl_fun E μ, 
            (∀ x : X, fun_sf (‖sf‖) x = (‖ fun_sf sf x ‖)%hy).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqf; rewrite <-Eqf => /=.
        unfold fun_sf.
        rewrite Eqf => //.
    Qed.

End simpl_fun_norm.

Notation "‖ f ‖" := (fun_norm f) (at level 100) : fun_scope.
Notation "‖ sf ‖" := (sf_norm_aux sf) (at level 100) : sf_scope.

Open Scope nat_scope.

Lemma le_lt_v_eq :
    ∀ k1 k2 : nat, k1 <= k2 ->
        k1 < k2 ∨ k1 = k2.
Proof. lia. Qed.

Close Scope nat_scope.

Section simpl_fun_plus.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope nat_scope.

    Definition fun_plus (f : X -> E) (g : X -> E) :=
        (fun x => plus (f x) (g x)).

    Notation "f + g" := (fun_plus f g) (left associativity, at level 50) : fun_scope. 

    Definition sf_plus_aux (sf sg : simpl_fun E μ) : simpl_fun E μ.
        case: sf => wf vf maxf axf1 axf2 axf3 axf4.
        case: sg => wg vg maxg axg1 axg2 axg3 axg4.
        pose val := fun m =>
            let (nf, ng) := square_bij_inv (S maxg) m in
            plus (vf nf) (vg ng).
        pose max_which := (S maxf) * (S maxg) - 1.
        pose which := fun (x : X) =>
            let nf := wf x in
            let ng := wg x in
            square_bij (S maxg) (nf, ng).
        apply (mk_simpl_fun which val max_which).
            (* ax_val_max_which *)
            unfold val, max_which.
            rewrite (square_bij_inv_corner maxg maxf).
            rewrite axf1 axg1 plus_zero_r; reflexivity.
            (* ax_which_max_which *)
            move => x; unfold which, max_which.
            apply confined_square.
            split; apply [axf2, axg2].
            (* ax_measurable *)
            1, 2 : assert
                (∀ n : nat, n <= max_which -> 
                ∀ c : nat * nat, c = square_bij_inv (S maxg) n ->
                ∀ nf ng : nat, (nf, ng) = c ->
                    measurable gen (λ x : X, wf x = nf ∧ wg x = ng)
                ) as measurable_inter_fg.
                1, 3 : move => n Hn c Eqc nf ng Hnfngc.
                1, 2 : pose Hnfng := confined_square_inv maxg maxf n Hn; clearbody Hnfng => /=.
                1, 2 : rewrite <-Eqc, <-Hnfngc in Hnfng.
                1, 2 : case: Hnfng => Hnf Hng.
                1, 2 : apply measurable_inter.
                1, 3 : apply axf3 => //.
                1, 2 : apply axg3 => //.

            move => n Hn; unfold which.
            pose c := square_bij_inv (S maxg) n.
            case_eq c => [nf ng] Eqc.
            apply measurable_ext with (fun x => wf x = nf ∧ wg x = ng).
            move => x.
            assert (n = square_bij (S maxg) c) as Eqn.
                rewrite is_bij_square_inv => //.
            rewrite Eqn Eqc.
            split.
                case => -> -> //. 
                move => Eqwn.
                assert (square_bij_inv (S maxg) (square_bij (S maxg) (wf x, wg x)) = square_bij_inv (S maxg) (square_bij (S maxg) (nf, ng))) 
                    by congruence.
                rewrite is_bij_square in H.
                    2 : apply axg2.
                rewrite is_bij_square in H.
                    all : swap 1 2.
                    pose Hng := confined_snd_square_inv maxg n.
                    fold c in Hng; clearbody Hng; rewrite Eqc in Hng.
                    exact Hng.
                split; congruence.
                apply measurable_inter_fg with n c => //.
            (* ax_finite *)
            move => n Hn; unfold which.
            pose c := square_bij_inv (S maxg) n.
            case_eq c => [nf ng] Eqc.
            assert (
                ∀ x : Rbar, Rbar_le (@zero R_AbelianGroup) x -> Rbar_lt x p_infty ->
                    is_finite x
            ) as Rbar_pos_lt_finite.
                move => x; case: x => //.
            apply Rbar_pos_lt_finite.
            apply meas_ge_0.
            assert (n = square_bij (S maxg) c).
                unfold c; rewrite is_bij_square_inv => //.
            rewrite H Eqc.
            replace
                (μ (λ x : X, square_bij (S maxg) (wf x, wg x) = square_bij (S maxg) (nf, ng)))
                with
                (μ (λ x : X, wf x = nf ∧ wg x = ng)).
                all : swap 1 2.
                apply measure_ext => x; split.
                    move => [-> ->] => //.
                    move => Eqfg.
                    assert 
                        (square_bij_inv (S maxg) (square_bij (S maxg) (wf x, wg x)) = square_bij_inv (S maxg) (square_bij (S maxg) (nf, ng)))
                        as Eqfg2 by congruence.
                    rewrite is_bij_square in Eqfg2.
                        2 : apply axg2.
                    rewrite is_bij_square in Eqfg2.
                        all : swap 1 2.
                        pose Hng := confined_snd_square_inv maxg n.
                        fold c in Hng; clearbody Hng; rewrite Eqc in Hng.
                        exact Hng.
                    split; congruence.
                (* Ici il faut distinguer le cas ou
                    on est dans la composante de 0 pour f ou pour g,
                    sachant que les deux ne peuvent pas se produire simultanément *)
                assert
                    (n <= max_which)
                    as Le_n_mw.
                    apply le_Sn_le => //.
                pose Hnfng := confined_square_inv maxg maxf n Le_n_mw; clearbody Hnfng.
                fold c in Hnfng; rewrite Eqc in Hnfng; case: Hnfng => Hnf Hng.
                assert
                    (Rbar_le 
                        (μ (λ x : X, wf x = nf ∧ wg x = ng))
                        (μ (λ x : X, wf x = nf))
                    ) as inter_le_f.
                    apply measure_le.
                    apply measurable_inter_fg with n c => //.
                    apply axf3 => //.
                    easy.
                assert
                (Rbar_le 
                    (μ (λ x : X, wf x = nf ∧ wg x = ng))
                    (μ (λ x : X, wg x = ng))
                ) as inter_le_g.
                    apply measure_le.
                    apply measurable_inter_fg with n c => //.
                    apply axg3 => //.
                    easy.
                case: (le_lt_v_eq nf maxf) => // Hnf'.
                    (* cas ou le dommaine pour f est mesurable *)
                    assert
                        (is_finite (μ (λ x : X, wf x = nf))) 
                        as fin_f.
                        apply axf4 => //.
                    assert
                        (Rbar_lt (μ (λ x : X, wf x = nf)) p_infty) as fin_f'.
                        unfold is_finite, real in fin_f.
                        rewrite <-fin_f => //.
                    apply (Rbar_le_lt_trans _ _ _ inter_le_f fin_f').
                    (* cas ou nf = maxf, donc où le domaine pour g est mesurable *)
                    assert (ng < maxg).
                        apply not_le => Hng'.
                        assert (ng = maxg) 
                            as Eqgng by apply Nat.le_antisymm => //.
                        rewrite Hnf' Eqgng in Eqc.
                        rewrite Eqc in H; rewrite square_bij_corner in H.
                        rewrite H in Hn; unfold max_which in Hn.
                        exact (Nat.Private_Tac.lt_irrefl Hn).
                    assert
                        (is_finite (μ (λ x : X, wg x = ng))) 
                        as fin_g.
                        apply axg4 => //.
                    assert
                        (Rbar_lt (μ (λ x : X, wg x = ng)) p_infty) as fin_g'.
                        unfold is_finite, real in fin_g.
                        rewrite <-fin_g => //.
                    apply (Rbar_le_lt_trans _ _ _ inter_le_g fin_g').
    Defined.

    Notation "sf + sg" := (sf_plus_aux sf sg) (left associativity, at level 50) : sf_scope.

    Lemma sf_plus :
        ∀ f g : X -> E, 
        is_simpl μ f -> is_simpl μ g ->
        is_simpl μ (fun_plus f g).
    Proof.
        move => f g.
        case => sf Eq_sf_f; case => sg Eq_sg_g.
        exists (sf_plus_aux sf sg).
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqf.
        case_eq sg => wg vg maxg axg1 axg2 axg3 axg4 Eqg.
        unfold fun_sf => /= x.
        rewrite is_bij_square.
            2 : apply axg2.
        unfold fun_plus.
        congr plus.
            unfold fun_sf in Eq_sf_f.
            rewrite Eqf in Eq_sf_f; simpl in Eq_sf_f.
            rewrite Eq_sf_f => //.
            unfold fun_sf in Eq_sg_g.
            rewrite Eqg in Eq_sg_g; simpl in Eq_sg_g.
            rewrite Eq_sg_g => //.
    Qed.

    Lemma fun_sf_plus :
        ∀ sf sg : simpl_fun E μ, 
            (∀ x : X, fun_sf (sf + sg)%sf x = (fun_sf sf x + fun_sf sg x)%hy).
    Proof.
        move => sf sg.
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqf; rewrite <-Eqf => /=.
        case_eq sg => wg vg maxg axg1 axg2 axg3 axg4 Eqg; rewrite <-Eqg => /=.
        unfold fun_sf.
        rewrite Eqf Eqg => x /=.
        rewrite is_bij_square => //.
    Qed.

End simpl_fun_plus.

Notation "f + g" := (fun_plus f g) (left associativity, at level 50) : fun_scope. 
Notation "sf + sg" := (sf_plus_aux sf sg) (left associativity, at level 50) : sf_scope.

Section simpl_fun_scal.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope nat_scope.

    Definition fun_scal (a : A) (g : X -> E) :=
        (fun x => scal a (g x)).

    Notation "a ⋅ g" := (fun_scal a g) (left associativity, at level 45) : fun_scope.

    Definition sf_scal_aux (a : A) (sf : simpl_fun E μ) : simpl_fun E μ.
        case: sf => wf vf maxf axf1 axf2 axf3 axf4.
        pose val := fun k => scal a (vf k).
        apply (mk_simpl_fun wf val maxf).
            unfold val; rewrite axf1 scal_zero_r => //.
            exact axf2.
            exact axf3.
            exact axf4.
    Defined.

    Notation "a ⋅ sf" := (sf_scal_aux a sf) (left associativity, at level 45) : sf_scope.

    Lemma sf_scal :
        ∀ a : A, ∀ f : X -> E, 
        is_simpl μ f ->
        is_simpl μ (fun_scal a f).
    Proof.
        move => a f.
        case => sf; case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqsf => /= Eqf.
        exists (sf_scal_aux a sf) => x.
        unfold fun_sf, val, which; rewrite Eqsf => /=.
        unfold fun_scal; rewrite Eqf => //.
    Qed.

    Lemma fun_sf_scal :
        ∀ a : A, ∀ sf : simpl_fun E μ, 
            (∀ x : X, fun_sf (a ⋅ sf) x = (a ⋅ (fun_sf sf x))%hy).
    Proof.
        move => a sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqf; rewrite <-Eqf => /=.
        unfold fun_sf.
        rewrite Eqf => //.
    Qed.

End simpl_fun_scal.

Notation "a ⋅ g" := (fun_scal a g) (left associativity, at level 45) : fun_scope.
Notation "a ⋅ sf" := (sf_scal_aux a sf) (left associativity, at level 45) : sf_scope.
Notation "- g" := (fun_scal (opp one) g) : fun_scope.
Notation "- sg" := (sf_scal_aux (opp one) sg) : sf_scope.
Notation "f - g" := (fun_plus f (- g)) : fun_scope.
Notation "sf - sg" := (sf_plus_aux sf (- sg)) : sf_scope.

Section simpl_fun_bounded.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope hy_scope.

    Definition sf_bounded :
        ∀ sf : simpl_fun E μ, { M : R | ∀ x : X, ‖ fun_sf sf x ‖ <= M }.
    (* definition *)
        move => sf.
        apply exist with (Rmax_n (fun k => ‖ val sf k ‖) (max_which sf)).
        move => x; unfold fun_sf.
        pose Hwx := ax_which_max_which sf x; clearbody Hwx.
        apply: fo_le_Rmax_n => //.
    Qed.

End simpl_fun_bounded.

Open Scope R_scope.
Open Scope nat_scope.

Lemma finite_sum_Rbar :
    ∀ u : nat -> Rbar, ∀ n : nat, (∀ k : nat, k ≤ n -> is_finite (u k))
    -> is_finite (sum_Rbar n u).
Proof.
    move => u; induction n => Hu.
        unfold sum_Rbar.
        assert (0 ≤ 0) by lia.
        apply Hu => //.
        simpl.
        assert (S n <= S n) by lia.
        pose HuSn := (Hu (S n) H); clearbody HuSn.
        assert (∀ k : nat, k ≤ n -> is_finite (u k)).
            move => k Hk.
            assert (k ≤ S n) by lia.
            apply Hu => //.
        pose Hsum := IHn H0; clearbody Hsum; clear H0.
        unfold is_finite in HuSn, Hsum |- *.
        rewrite <-HuSn, <-Hsum => //.
Qed.

Section simpl_fun_meas.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma measurable_sf_preim :
        ∀ sf : simpl_fun E μ, ∀ y : E,
            measurable gen (fun x : X => sf x = y).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqf; rewrite <-Eqf => /=.
        move => y.
        pose P := fun k => (λ x : X, vf k = y ∧ which sf x = k).
        apply measurable_ext with (λ x : X, ∃ k : nat, k ≤ maxf ∧ P k x).
            move => x; split.
                case => k; case => Hk.
                unfold P; case => <-; unfold fun_sf => ->.
                rewrite Eqf => /=; split; auto with arith.
                move => Eq_sfx_vfn.
                exists (which sf x); split.
                    replace (which sf x) with (wf x) by rewrite Eqf => //; apply axf2.
                    unfold P; split.
                    unfold fun_sf in Eq_sfx_vfn.
                    replace (vf (which sf x)) with (val sf (which sf x))
                        by rewrite Eqf => //.
                    rewrite Eq_sfx_vfn => //.
                    reflexivity.
                apply measurable_union_finite => k Hk.
                unfold P; apply measurable_inter.
        apply measurable_Prop.
        replace (which sf) with (wf) by rewrite Eqf => //.
        apply axf3 => //.
    Qed.

    Lemma sf_measurable_preim_le :
        ∀ sf : simpl_fun E μ, ∀ n : nat, n ≤ max_which sf ->
            measurable gen (λ x : X, which sf x ≤ n).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqf; rewrite <-Eqf => /=.
        move => n Hn.
        pose B := fun k => (λ x : X, which sf x = k).
        apply measurable_ext with (fun x => ∃ k : nat, k ≤ n ∧ which sf x = k).
            move => x; split.
                case => k [Hk Eqk]; lia.
                move => Hsfx; exists (which sf x); auto.
            apply (measurable_union_finite _ ) => k Hk.
            apply ax_measurable.
            lia.
    Qed.

    Lemma sf_measurable_preim_lt :
        ∀ sf : simpl_fun E μ, ∀ n : nat, n ≤ max_which sf ->
            measurable gen (λ x : X, which sf x < n).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqf; rewrite <-Eqf => /=.
        case.
            move => _.
            apply measurable_ext with (fun _ => False).
            move => x; split => //.
            lia.
            apply measurable_Prop.
            
            move => n' HSn'.
            apply measurable_ext with (fun x => which sf x ≤ n').
            move => x; split; lia.
            apply sf_measurable_preim_le; lia.
    Qed.

    Lemma is_finite_sf_preim_lt :
        ∀ sf : simpl_fun E μ, ∀ n : nat, n ≤ max_which sf ->
            is_finite (μ (λ x : X, which sf x < n)).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqf; rewrite <-Eqf => /=.
        case.
            move => _.
            rewrite (measure_ext _ _ _ (fun _ => False)).
            rewrite meas_False => //.
            lia.
        move => n Hn.
        rewrite (measure_ext _ _ _ (λ x : X, which sf x ≤ n)); swap 1 2.
            lia.
        pose B := fun k => (λ x : X, which sf x = k).
        rewrite (measure_decomp_finite _  μ _ maxf B).
        assert (n < maxf) as Ltnmaxf.
        rewrite Eqf in Hn; simpl in Hn.
        lia.
        apply finite_sum_Rbar => k Hk; unfold B.
        case_eq (k <=? n).
            move => /Nat.leb_le Hk'.
            rewrite (measure_ext _ _ _ (fun x => which sf x = k)).
            apply ax_finite; lia.
            move => x; split; [easy | move => -> //].
            move => /Nat.leb_gt Hk'.
            rewrite (measure_ext _ _ _ (fun _ => False)).
            rewrite meas_False => //.
            move => x; split => //.
            lia.
        apply sf_measurable_preim_le; lia.
        move => k Hk; unfold B; apply ax_measurable; rewrite Eqf => //.
        move => x; unfold B; exists (which sf x); split => //.
        rewrite Eqf => /=; apply axf2.

        move => p q x Hp Hq; unfold B; move => -> //.
    Qed.

    Lemma sf_decomp_preim_which :
        ∀ sf : simpl_fun E μ, ∀ y : E,
            (μ (fun x : X => sf x = y)) 
            = sum_Rbar (max_which sf) (fun k => (μ (fun x : X => val sf k = y ∧ which sf x = k))).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqf; rewrite <-Eqf => /=.
        move => y.
        pose B := fun k => (λ x : X, which sf x = k).
            rewrite (measure_decomp_finite _ μ (fun x => sf x = y) maxf B).
            unfold B; rewrite Eqf => /=.
            apply sum_Rbar_ext => k Hk.
            apply measure_ext => x; split.
                case => Eq_sfx_y Eq_wfx_k.
                split; [rewrite <-Eq_wfx_k | rewrite Eq_wfx_k] => //.
                case => Eq_vfk_y Eq_wfx_k.
                split; [rewrite Eq_wfx_k | ] => //.
            apply measurable_sf_preim.
            move => k Hk.
            unfold B; apply ax_measurable; rewrite Eqf => //.
            move => x; unfold B; exists (which sf x).
            split; [rewrite Eqf => /=; apply axf2 | reflexivity].
            move => p q x Hp Hq; unfold B => -> //.
    Qed.

    Lemma finite_sf_preim_neq_0 :
        ∀ sf : simpl_fun E μ, ∀ y : E, y ≠ zero ->
            is_finite (μ (fun x : X => sf x = y)).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqf; rewrite <-Eqf => /=.
        move => y Hy.
        rewrite sf_decomp_preim_which.
        apply finite_sum_Rbar => k Hk.
        case: (le_lt_or_eq k (max_which sf) Hk) => Hkmaxf.
            apply Rbar_bounded_is_finite with (real 0%R) (μ (λ x : X, which sf x = k)).
            apply meas_ge_0.
            apply (measure_le _ μ (λ x : X, val sf k = y ∧ which sf x = k) (fun x => which sf x = k)).
            apply measurable_inter.
            apply measurable_Prop.
            1, 2 : rewrite Eqf => /=; apply axf3; rewrite Eqf in Hk; simpl in Hk => //.
            move => x; case; auto.
            easy.
            apply ax_finite => //.
        
            rewrite (measure_ext _ _ _ (fun _ => False)).
            rewrite meas_False => //.
            move => x; split => //.
            case; move => Abs _.
            rewrite Hkmaxf in Abs.
            rewrite <-Abs in Hy.
            rewrite Eqf in Hy; simpl in Hy => //.
    Qed.

    (*
    Lemma measurable_fun_sf :
        ∀ s : simpl_fun E μ,
            measurable_fun gen open s.
    Admitted.
    *)

End simpl_fun_meas.