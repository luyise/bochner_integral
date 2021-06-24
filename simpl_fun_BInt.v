Add LoadPath "~/Documents/CoqNotGit/LInt/LInt_p" as MILC.

From Coq Require Import 
    ssreflect
    ssrsearch
    Lia
    Utf8

    Rdefinitions
.

From Coquelicot Require Import
    Hierarchy
    Rbar
.

From MILC Require Import 
    measure
    sigma_algebra
    sum_Rbar_nonneg
.

Require Import 
    simpl_fun
    square_bij
    hierarchy_notations
.

Open Scope hy_scope.

Section BInt_for_sf.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope R_scope.

    (* Une définition calculable de l'intégrale de Bochner d'une fonction simple *)
    Definition BInt_sf (sf : simpl_fun _ μ) : E :=
        sum_n
            (fun n => scal (real (μ (nth_carrier sf n))) (sf.(val) n))
            (sf.(max_which)).

    (*
    Lemma BInt_sf_indep_of_dec :
        ∀ f : X -> E, ∀ l l' : list ((X -> Prop) * E),
        ∀ π : simpl_fun_for μ l f, ∀ π' : simpl_fun_for μ l' f,
        BInt_sf f l π = BInt_sf f l' π'.
    *)
    (* Idées pour s'y prendre avec ce lemme :
        1. s'en sortir avec un lemme d'extensionnalité (violent)
            ça doit être faisable avec la définition des fonctions simples
        2. commencer par montrer que cette définition est un morphisme pour +
            et remarquer que f - f admet une décomposition triviale donnant une intégrale nulle 
    *)

End BInt_for_sf.

Notation "'∫B' sf" := (BInt_sf sf)
        (only printing, at level 45, format "'[ ' '∫B'  sf ']'") : sf_scope.

Open Scope nat_scope.

Lemma sum_n_m_scal_r {A : Ring} {E : ModuleSpace A} :
    ∀ a : nat -> A, ∀ u : E, ∀ n m : nat,
        sum_n_m (fun k : nat => scal (a k) u) n m = scal (sum_n_m (fun k : nat => (a k)) n m) u.
Proof.
    move => a u n.
    induction n => m.
        induction m.
        do 2 rewrite sum_n_n => //.
        rewrite sum_n_Sm. 2 : lia.
        rewrite sum_n_Sm. 2 : lia.
        rewrite scal_distr_r.
        rewrite IHm => //.
    case_eq (n <=? m).
        move /Nat.leb_le => Hnm.
        pose IHnm := IHn m; clearbody IHnm.
        rewrite sum_Sn_m in IHnm. 2 : lia.
        rewrite [in RHS]sum_Sn_m in IHnm. 2 : lia.
        rewrite scal_distr_r in IHnm.
        apply (plus_reg_l (scal (a n) u)) => //.
        move /Nat.leb_gt => Hmn.
        rewrite sum_n_m_zero. 2 : lia.
        rewrite sum_n_m_zero. 2 : lia.
        rewrite scal_zero_l => //.
Qed.

Lemma sum_n_scal_r {A : Ring} {E : ModuleSpace A} :
    ∀ a : nat -> A, ∀ u : E, ∀ n m : nat,
        sum_n (fun k : nat => scal (a k) u) n = scal (sum_n (fun k : nat => (a k)) n) u.
Proof.
    unfold sum_n => a u n m.
    apply sum_n_m_scal_r.
Qed.

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
        

Lemma sum_n_sum_Rbar :
    ∀ u : nat -> Rbar, ∀ n : nat, (∀ k : nat, k <= n -> is_finite (u k))
    -> sum_n (fun k => real (u k)) n = real (sum_Rbar n u).
Proof.
    induction n.
        rewrite sum_O.
        unfold sum_Rbar => //.
        move => Hu.
        rewrite sum_Sn.
        rewrite IHn.
            all : swap 1 2.
            move => k Hkn.
            assert (k <= S n) by lia.
        apply Hu => //; clear Hu.
        assert (S n <= S n) by lia.
        pose Le0uSn := Hu (S n) H; clearbody Le0uSn; clear H.
        assert (∀ k : nat, k ≤ n -> is_finite (u k)).
            move => k Hk.
            assert (k ≤ S n) by lia.
            apply Hu => //.
        pose Le0sum := finite_sum_Rbar u n H; clearbody Le0sum; clear H.
        simpl; rewrite Rbar_plus_comm.
        unfold Rbar_plus, Rbar_plus'.
        unfold is_finite in Le0sum, Le0uSn.
        rewrite <-Le0uSn, <-Le0sum => //.
Qed.

Section BInt_sf_plus.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope R_scope.
    Open Scope nat_scope.
    Open Scope sf_scope.

    Lemma BInt_sf_plus_aux :
        ∀ sf_f sf_g : simpl_fun E μ,
            BInt_sf (sf_f + sf_g) = ((BInt_sf sf_f) + (BInt_sf sf_g))%hy.
    Proof.
        move => sf_f sf_g.
        case_eq sf_f => wf vf maxf axf1 axf2 axf3 axf4 Eqf.
        case_eq sf_g => wg vg maxg axg1 axg2 axg3 axg4 Eqg.
        rewrite <-Eqf, <- Eqg.
        unfold BInt_sf.
        replace (max_which sf_f) with maxf by rewrite Eqf => //.
        replace (max_which sf_g) with maxg by rewrite Eqg => //.
        replace (max_which (sf_f + sf_g)) with ((S maxf) * (S maxg) - 1).
            2 : rewrite Eqf Eqg => //.
        unfold nth_carrier.
        rewrite square_bij_sum.
        pose valfg := val (sf_f + sf_g).
            fold valfg.
            assert (valfg = simpl_fun.val (sf_f + sf_g))
                as Eqval by unfold valfg => //.
            clearbody valfg; rewrite Eqf Eqg in Eqval; simpl in Eqval.
            rewrite Eqval; clear Eqval valfg.
        pose whichfg := which (sf_f + sf_g).
            fold whichfg.
            assert (whichfg = which (sf_f + sf_g))
                as Eqwhich by unfold whichfg => //.
            clearbody whichfg; rewrite Eqf Eqg in Eqwhich; simpl in Eqwhich.
            rewrite Eqwhich; clear Eqwhich whichfg.
        assert 
            (∀ k1 k2 : nat, k2 <= maxg ->
                (μ
                    (λ x : X,
                        square_bij (S maxg) (wf x, wg x) =
                        square_bij (S maxg) (k1, k2))
                ) =
                (μ
                    (λ x : X,
                        wf x = k1 ∧ wg x = k2
                    )
                )
            ) as Eqμ.
            move => k1 k2 Hk2.
            apply measure_ext => x; split.
                move => Eqwfk.
                assert 
                    (square_bij_inv (S maxg) 
                        (square_bij (S maxg) (wf x, wg x))
                    =
                    square_bij_inv (S maxg) 
                        (square_bij (S maxg) (k1, k2))
                    ) as Eqaux by congruence.
                rewrite is_bij_square in Eqaux.
                    2 : apply axg2.
                rewrite is_bij_square in Eqaux.
                    2 : assumption.
                split; congruence.
                case => -> -> //.
        assert 
            (∀ k1 k2 : nat, k2 <= maxg ->
                (let (nf, ng) :=
                    square_bij_inv (S maxg) (square_bij (S maxg) (k1, k2)) in
                    plus (vf nf) (vg ng))
                = plus (vf k1) (vg k2)
            ) as Eqsum.
            move => k1 k2 Hk2.
            rewrite is_bij_square.
                2 : assumption.
            reflexivity.
        assert 
            (∀ k1 k2 : nat, k2 <= maxg ->
                scal
                    (real (μ
                    (λ x : X,
                        square_bij (S maxg) (wf x, wg x) =
                        square_bij (S maxg) (k1, k2))))
                    (let (nf, ng) :=
                    square_bij_inv (S maxg) (square_bij (S maxg) (k1, k2)) in
                    plus (vf nf) (vg ng))
                =
                scal
                    (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                    (plus (vf k1) (vg k2))
            ) as Eqsum1.
            move => k1 k2 Hk2.
            rewrite Eqsum. 2 : assumption.
            rewrite Eqμ. 2 : assumption.
            reflexivity.
        clear Eqsum Eqμ.
        assert 
            (∀ k1 : nat, 
                sum_n
                    (λ k2 : nat,
                        scal
                            (real (μ
                            (λ x : X,
                                square_bij (S maxg) (wf x, wg x) =
                                square_bij (S maxg) (k1, k2))))
                            (let (nf, ng) :=
                            square_bij_inv (S maxg) (square_bij (S maxg) (k1, k2)) in
                            plus (vf nf) (vg ng))
                    ) maxg
                =
                sum_n
                    (λ k2 : nat,
                        scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (plus (vf k1) (vg k2))
                    ) maxg
            ) as Eqsum.
            move => k1.
            apply sum_n_ext_loc => k2 Hk2.
            apply Eqsum1 => //.
        assert
            (sum_n
            (λ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        scal
                        (real (μ
                            (λ x : X,
                            square_bij (S maxg) (wf x, wg x) =
                            square_bij (S maxg) (k1, k2))))
                        (let (nf, ng) :=
                            square_bij_inv (S maxg) (square_bij (S maxg) (k1, k2)) in
                            plus (vf nf) (vg ng))
                    ) maxg
                ) maxf
            =
            sum_n
            (λ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        scal
                        (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                        (plus (vf k1) (vg k2))
                    ) maxg
                ) maxf
            ) as Rwrt
            by apply sum_n_ext => //.
        rewrite Rwrt; clear Rwrt Eqsum Eqsum1.
        assert
            (∀ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        scal 
                        (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                        (plus (vf k1) (vg k2))
                ) maxg
                =
                sum_n
                    (λ k2 : nat,
                        plus
                            (scal 
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vf k1))
                            (scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vg k2))
                ) maxg
            ) as Eqsum.
            move => k1.
            apply sum_n_ext_loc => k2 Hk2.
            rewrite scal_distr_l => //.
        assert
            (sum_n
                (λ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        scal 
                        (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                        (plus (vf k1) (vg k2))
                ) maxg
            ) maxf
            =
            sum_n
                (λ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        plus
                            (scal 
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vf k1))
                            (scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vg k2))
                ) maxg
            ) maxf
            ) as Rwrt
            by apply sum_n_ext => //.
        rewrite Rwrt; clear Rwrt Eqsum.
        assert
            (∀ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        plus 
                            (scal 
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vf k1))
                            (scal 
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vg k2))
                ) maxg
                =
                plus
                    (sum_n
                        (λ k2 : nat,
                            scal 
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vf k1)
                    ) maxg)
                    (sum_n
                        (λ k2 : nat,
                            scal 
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vg k2)
                    ) maxg)
            ) as Eqsum.
            move => k1.
            apply sum_n_plus.
        assert
            (sum_n
                (λ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        plus 
                            (scal 
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vf k1))
                            (scal 
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vg k2))
                ) maxg
            ) maxf
            =
            plus
                (sum_n
                    (λ k1 : nat,
                    sum_n
                        (λ k2 : nat,
                            scal 
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vf k1)
                    ) maxg
                ) maxf)
                (sum_n
                    (λ k1 : nat,
                    sum_n
                        (λ k2 : nat,
                            scal 
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vg k2)
                    ) maxg
                ) maxf)
            ) as Rwrt.
            rewrite <-sum_n_plus.
            apply sum_n_ext_loc => k1 //.
        rewrite Rwrt.
        clear Rwrt Eqsum.
        (* Etape mathématiquement importante ! *)
        setoid_rewrite sum_n_switch at 2.
        assert
            (sum_n
                (λ j : nat,
                sum_n (λ i : nat, scal (real (μ (λ x : X, wf x = i ∧ wg x = j))) (vg j))
            maxf) maxg
            =
            sum_n
                (λ k2 : nat,
                scal 
                    (sum_n (λ k1 : nat, (real (μ (λ x : X, wf x = k1 ∧ wg x = k2))))
                    maxf)
                    (vg k2)
            ) maxg
            ) as Eqsum.
            apply sum_n_ext => n.
            rewrite sum_n_scal_r => //.
        rewrite Eqsum; clear Eqsum.
        assert
            (sum_n
                (λ k1 : nat,
                sum_n (λ k2 : nat, scal (real (μ (λ x : X, wf x = k1 ∧ wg x = k2))) (vf k1))
            maxg) maxf
            =
            sum_n
                (λ k1 : nat,
                scal 
                    (sum_n (λ k2 : nat, (real (μ (λ x : X, wf x = k1 ∧ wg x = k2))))
                    maxg)
                    (vf k1)
            ) maxf
            ) as Eqsum.
            apply sum_n_ext => n.
            rewrite sum_n_scal_r => //.
        rewrite Eqsum; clear Eqsum.
        assert
            (∀ k1 k2 : nat, k1 ≤ maxf -> k2 ≤ maxg ->
                measurable gen (λ x : X, wf x = k1 ∧ wg x = k2)
            ) as measurable_inter_fg.
                move => k1 k2 Hk1 Hk2.
                apply measurable_inter.
                1, 2 : apply [axf3, axg3] => //.
        congr plus; apply sum_n_ext_loc.
            replace (val sf_f) with vf by rewrite Eqf => //.
            move => k1 Hk1.
            case (le_lt_v_eq k1 maxf) => //.
                move => Hk1'.
                congr scal.
                replace (which sf_f) with wf by rewrite Eqf => //.
                rewrite sum_n_sum_Rbar.
                    all : swap 1 2.
                    move => k2 Hk2.
                    assert
                        (Rbar_le 
                            (μ (λ x : X, wf x = k1 ∧ wg x = k2))
                            (μ (λ x : X, wf x = k1))
                        ) as inter_le_f.
                        apply measure_le.
                        apply measurable_inter_fg => //.
                        apply axf3 => //.
                        easy.
                    pose fin_μ_f := axf4 k1 Hk1'; clearbody fin_μ_f.
                    unfold is_finite in fin_μ_f; rewrite <-fin_μ_f in inter_le_f.
                    unfold real in inter_le_f.
                    unfold is_finite, real.
                    case_eq (μ (λ x : X, wf x = k1 ∧ wg x = k2)) => //.
                        move => Abs_μ; apply False_ind.
                        rewrite Abs_μ in inter_le_f => //.
                        move => Abs_μ; apply False_ind.
                        pose Ge0μ := meas_ge_0 gen μ (λ x : X, wf x = k1 ∧ wg x = k2); clearbody Ge0μ.
                        rewrite Abs_μ in Ge0μ => //.
                    rewrite (measure_decomp_finite gen μ (fun (x : X) => wf x = k1) maxg (fun k2 => (fun (x : X) => wg x = k2))) => //.
                        apply axf3 => //.
                        move => x; exists (wg x); split => //.
                        move => n p x _ _ -> //.
                move => ->.
                rewrite axf1; do 2 rewrite scal_zero_r => //.
            replace (val sf_g) with vg by rewrite Eqg => //.
            move => k2 Hk2.
            case (le_lt_v_eq k2 maxg) => //.
                move => Hk2'.
                congr scal.
                replace (which sf_g) with wg by rewrite Eqg => //.
                rewrite sum_n_sum_Rbar.
                    all : swap 1 2.
                    move => k1 Hk1.
                    assert
                        (Rbar_le 
                            (μ (λ x : X, wf x = k1 ∧ wg x = k2))
                            (μ (λ x : X, wg x = k2))
                        ) as inter_le_g.
                        apply measure_le.
                        apply measurable_inter_fg => //.
                        apply axg3 => //.
                        easy.
                    pose fin_μ_g := axg4 k2 Hk2'; clearbody fin_μ_g.
                    unfold is_finite in fin_μ_g; rewrite <-fin_μ_g in inter_le_g.
                    unfold real in inter_le_g.
                    unfold is_finite, real.
                    case_eq (μ (λ x : X, wf x = k1 ∧ wg x = k2)) => //.
                        move => Abs_μ; apply False_ind.
                        rewrite Abs_μ in inter_le_g => //.
                        move => Abs_μ; apply False_ind.
                        pose Ge0μ := meas_ge_0 gen μ (λ x : X, wf x = k1 ∧ wg x = k2); clearbody Ge0μ.
                        rewrite Abs_μ in Ge0μ => //.
                    rewrite (measure_decomp_finite gen μ (fun (x : X) => wg x = k2) maxf (fun k1 => (fun (x : X) => wf x = k1))) => //.
                        rewrite (sum_Rbar_ext maxf (λ n : nat, μ (λ x : X, wg x = k2 ∧ wf x = n)) (λ k : nat, μ (λ x : X, wf x = k ∧ wg x = k2))).
                        all : swap 1 2.
                        move => i Hi.
                        apply measure_ext => x.
                        split; case => //.
                        reflexivity.
                        apply axg3 => //.
                        move => x; exists (wf x); split => //.
                        move => n p x _ _ -> //.
                move => ->.
                rewrite axg1; do 2 rewrite scal_zero_r => //.
    Qed.
                
End BInt_sf_plus.

Section BInt_sf_scal.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope R_scope.
    Open Scope nat_scope.
    Open Scope sf_scope.

    Lemma BInt_sf_scal_aux :
        ∀ a : R_AbsRing, ∀ sf : simpl_fun E μ,
            BInt_sf (a ⋅ sf) = (a ⋅ (BInt_sf sf))%hy.
    Proof.
        move => a sf.
        unfold BInt_sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 axf4 Eqsf; rewrite <-Eqsf.
        rewrite <-sum_n_scal_l.
        replace (max_which (a ⋅ sf)) with (max_which sf)
            by rewrite Eqsf => //.
        apply sum_n_ext => k.
        unfold nth_carrier.
        replace (which (a ⋅ sf)) with (which sf)
            by rewrite Eqsf => //.
        replace (val (a ⋅ sf) k) with (scal a (val sf k))
            by rewrite Eqsf => //.
        do 2 rewrite scal_assoc.
        replace mult with Rmult by easy.
        rewrite Raxioms.Rmult_comm.
        replace (@mult R_AbsRing) with Rmult by easy.
        reflexivity.
    Qed.

End BInt_sf_scal.

Section BInt_linearity.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope R_scope.
    Open Scope nat_scope.
    Open Scope sf_scope.

    Lemma BInt_sf_lin_aux :
        ∀ a b : R_AbsRing, ∀ sf sg : simpl_fun E μ,
            BInt_sf (a ⋅ sf + b ⋅ sg) 
            = ((a ⋅ (BInt_sf sf)) + (b ⋅ (BInt_sf sg)))%hy.
    Proof.
        move => a b sf sg.
        do 2 rewrite <-BInt_sf_scal_aux.
        rewrite BInt_sf_plus_aux => //.
    Qed.

End BInt_linearity.