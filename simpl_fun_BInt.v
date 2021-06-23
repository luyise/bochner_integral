Add LoadPath "~/Documents/CoqNotGit/LInt/LInt_p" as MILC.

From Coq Require Import 
    ssreflect
    ssrsearch
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
.

Require Import 
    simpl_fun
    square_bij
.

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

    (* Une définition un peu lourde mais calculable de l'intégrale de Boshner pour une fonction simple *)
    Definition BInt_sf (sf : @simpl_fun _ _ E _ μ) : E :=
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

Section Bint_sf_plus.

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

    (*

    Lemma BInt_sf_plus_aux :
        ∀ sf_f sf_g : @simpl_fun _ _ E _ μ,
            BInt_sf (simpl_fun_plus_aux sf_f sf_g) = plus (BInt_sf sf_f) (BInt_sf sf_g).
    Proof.
        move => sf_f sf_g.
        case_eq sf_f => wf vf maxf axf1 axf2 axf3 axf4 Eqf.
        case_eq sf_g => wg vg maxg axg1 axg2 axg3 axg4 Eqg.
        rewrite <-Eqf, <- Eqg.
        unfold BInt_sf.
        replace (max_which sf_f) with maxf by rewrite Eqf => //.
        replace (max_which sf_g) with maxg by rewrite Eqg => //.
        replace (max_which (simpl_fun_plus_aux sf_f sf_g)) with ((S maxf) * (S maxg) - 1).
            2 : rewrite Eqf Eqg => //.
        unfold nth_carrier.
        rewrite square_bij_sum.
        pose valfg := val (simpl_fun_plus_aux sf_f sf_g).
            fold valfg.
            assert (valfg = simpl_fun.val (simpl_fun_plus_aux sf_f sf_g))
                as Eqval by unfold valfg => //.
            clearbody valfg; rewrite Eqf Eqg in Eqval; simpl in Eqval.
            rewrite Eqval; clear Eqval valfg.
        pose whichfg := which (simpl_fun_plus_aux sf_f sf_g).
            fold whichfg.
            assert (whichfg = which (simpl_fun_plus_aux sf_f sf_g))
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
        clear Eqsum. clear Eqμ.
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

    *)
                
End Bint_sf_plus.