
Add LoadPath "~/Documents/CoqNotGit/LInt/LInt_p" as MILC.

(* 
On pourrait ne choisir de prendre que des parties définies décidablement,
pour simplifier le développement, on utilise l'axiome du tier exclu : 
    [ ∀ P : Prop, {P} + {¬ P} ]
*)

From Coq Require Import 
    ssreflect
    ssrsearch
    Utf8

    ClassicalDescription

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

Require Import sum_list.

(* Une tentative qui n'a pas fonctionné

Section simpl_fun_def.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.

    Definition indic (P : X -> Prop) : X -> A :=
        fun x =>
            match (excluded_middle_informative (P x)) return A with
                | left _ => one
                | right _ => zero
            end.

    Definition simpl_fun (f : X -> E) : Prop :=
        ∃ (l : list (prod (X -> Prop) E)),
            (∀ x : X,
                f x = sum_list (List.map 
                    (fun e => match e with (P, v) => scal ((indic P) x) v end) l)).

End simpl_fun_def.

Section simpl_fun_norm.

    Open Scope list_scope.

    Eval compute in (List.list_power (9::8::7::nil) (1::0::nil)).

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.

    Definition fun_norm (f : X -> E) :=
        fun x => norm (f x).

    (* 
    On écrit une fonction qui prend comme paramètre une (list (X -> Prop) * E * nat)
    que l'on note ici
            [(P₁, v₁, ϵ₁), (P₂, v₂, ϵ₂), ... , (Pₙ, vₙ, ϵₙ)]
    dont le deuxième argument est entre 0 et 1, et qui renvoie un élément de type (X -> Prop) * E qui est
            (ϵ₁¬ P₁ ∧ ϵ₂¬ P₂, ∧ ... ∧ ϵₙ¬ Pₙ, ∑ (1-ϵᵢ)⋅vᵢ )
    où ϵ¬ P signinfie
        P si ϵ = 0,
        ¬ P sinon.
    *)
    
    Open Scope type_scope.
    Open Scope core_scope.

    Fixpoint conj_and_sum (l : list ((X -> Prop) * E * nat)) : (X -> Prop) * E :=
        match l return (X -> Prop) * E with
            | nil => ((fun (x : X) => True), zero)
            | t :: tail =>
                match t with (P, v, n) =>
                    let (Q, w) := (conj_and_sum tail) in
                    match n with
                        | O => (fun (x : X) => P x ∧ Q x, plus v w)
                        | _ => (fun (x : X) => (¬ P x) ∧ Q x, w)
                    end
                end
        end.

    (* 
        On exprime le fait qu'étant donné une fonction simple, on peut décomposer son support en
        intersection des différents support des indicdatrice dont elle est combinaison linéaire
    *)
    Lemma simpl_fun_decomposition :
        ∀ f : X -> E, ∀ l : list ((X -> Prop) * E),
            (
                ∀ x : X,
                f x = sum_list 
                (
                    List.map 
                    (fun e => match e with (P, v) => scal ((indic P) x) v end)
                    l
                )
            )
            ->
            (
                let pl := List.list_power l (1::0::nil) in
                let conj_and_sum_list := List.map conj_and_sum pl in
                (
                    ∀ x : X, f x = sum_list
                        ( 
                            List.map 
                            (fun e => match e with (P, v) => scal ((indic P) x) v end)
                            conj_and_sum_list
                        )
                )
            ).
    Proof.
        move => f l.
        move: f.
        induction l.
        (* Cas de la liste nil *)
            move => /= f Hf x.
            rewrite scal_zero_r.
            rewrite plus_zero_r.
            move: x; assumption.
        (* Cas de la liste (a :: l) *)
            case: a => [P v] f => /= Hf x.
            unfold conj_and_sum.
            simpl in pl.
            unfold List.flat_map in pl; simpl in pl.
            unfold List.list_power in pl.
            simpl in pl.

            (* case l eqn: Hl => /= Hf x.
            pose Hfx := Hf x; clearbody Hfx.
                rewrite plus_zero_r in Hfx.
                rewrite scal_zero_r.
                do 2 rewrite plus_zero_r.
                rewrite plus_zero_l.
                assert (indic P x) *) 

            unfold List.flat_map => /=.
            unfold List.list_power.
            pose g := 
                fun x => 
                (
                    sum_list
                    (
                        List.map
                        (λ e : (X → Prop) * E, let (P, v) := e in scal (indic P x) v)
                        l
                    )
                ).
            assert ((∀ x : X,
                g x =
                sum_list
                (List.map
                    (λ e : (X → Prop) * E, let (P, v) := e in scal (indic P x) v)
                    l))) as Hg.
                unfold g => y; reflexivity.
            
            pose Hg' := IHl g Hg; clearbody Hg'; clear Hg; rename Hg' into Hg.
            simpl in Hg.
            pose Hgx := Hg x; clearbody Hgx.
            case (List.list_power l (1 :: 0 :: nil)) eqn: Hl => /=.
                simpl in *.
                unfold g in Hgx; clear Hg.
                assert
                    (g x = sum_list
                    (List.map
                       (λ e : (X → Prop) * E, let (P, v) := e in scal (indic P x) v) l)) as Defg.
                    unfold g; reflexivity.
                rewrite Hgx in Defg.
                assert 
                    (
                        f x = plus (scal (indic P x) v)
                        (sum_list
                           (List.map
                              (λ e : (X → Prop) * E, let (P, v) := e in scal (indic P x) v)
                              l))
                    ) 
                    as Hfx
                    by apply Hf.
                
                rewrite Hgx in Hfx.
                rewrite plus_zero_r in Hfx.
            unfold conj_and_sum.
            
            rewrite List.map_cons.

    Lemma fun_norm_simpl :
        ∀ f : X -> E, simpl_fun f -> simpl_fun (fun_norm f).
    Proof.
        move => f; case => l.
        pose power_listParts := List.list_power l (1::0::nil).
        pose conj_and_sum_list := List.map conj_and_sum power_listParts.
        move => f_simpl.
        assert 
            (∀ x : X, f x = sum_list (List.map 
            (fun e => match e with (P, v) => scal ((indic P) x) v end) conj_and_sum_list)) as f_is_piecewise_constant.

            move => x.

            pose decide := fun (c : (X -> Prop) * E) => 
                match (excluded_middle_informative (fst c x)) return nat with
                    | left _ => O
                    | right _ => 1
                end.
            pose case_list := List.map decide l.


        
        apply (lin_comb (fun_norm f) 
            (List.map (fun (c : (X -> Prop) * E) => let (P, v) := c in (P, norm v)) conj_and_sum_list)).

End simpl_sum_norm.

*)

(* 
Une deuxième tentative !


Section simpl_fun_def.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.

    Definition indic (P : X -> Prop) : X -> A :=
        fun x =>
            match (excluded_middle_informative (P x)) return A with
                | left _ => one
                | right _ => zero
            end.

    Open Scope R_scope.
    Open Scope core_scope.
    Open Scope type_scope.
    
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context (μ : measure gen).

    Inductive Unique {T : Type} (P : T -> Prop) : list T -> Prop := 
        | Unique_base_case : ∀ (x : T), ∀ (tail : list T), 
            P x -> List.Forall (fun y => ¬ (P y)) tail -> Unique P (x :: tail) 
        | Unique_inductive_case : ∀ (x : T), ∀ (tail : list T),
            ¬ (P x) -> Unique P tail -> Unique P (x :: tail).

    Definition disjoint (l : list (X -> Prop)) : Prop :=
        ∀ x : X,
            (List.Forall (fun P => ¬ P x) l)
            ∨
            (Unique (fun P => P x) l).

    Definition finite_measured (P : X -> Prop) : Prop :=
        is_finite (μ P).
    (* ∃ x : R, (μ P) = Finite x *)

    Definition well_formed_decomposition (l : list (X -> Prop)) : Prop :=
        disjoint l ∧ 
        List.Forall (measurable gen) l ∧
        List.Forall (finite_measured) l.

    Open Scope list_scope.

    Lemma well_formed_tail
        {l : list (X -> Prop)} {P : X -> Prop} :  
        well_formed_decomposition (P :: l) -> well_formed_decomposition l.
    Proof.
        move => wf_lext; repeat split.
            (* caractère disjoint *)
            case: wf_lext => Disj _.
            unfold disjoint in Disj |- * => x.
            case: (Disj x); clear Disj.
                move => case_out; left.
                apply (List.Forall_inv_tail case_out).
                move => case_in.
                inversion case_in.
                    clear H H0; clear x0 tail H1.
                    left; assumption.
                    clear H H0; clear x0 tail H1.
                    right; assumption.
            
            case: wf_lext => _ [Mlext _].
            apply (List.Forall_inv_tail Mlext).

            case: wf_lext => _ [_ Flext].
            apply (List.Forall_inv_tail Flext).
    Qed.

    Definition simpl_fun_for (l : list ((X -> Prop) * E)) (f : X -> E) :=
        well_formed_decomposition (List.map fst l) ∧
        (∀ x : X,
            (List.Forall
                (fun (c : (X -> Prop) * E) => 
                    let (P, v) := c in
                    P x -> f x = v
                )
                l
            )
        )
        ∧
        (∀ x : X, 
            (List.Forall
                (fun (c : (X -> Prop) * E) =>
                    let (P, v) := c in
                    ¬ P x
                )
                l
            -> f x = zero)
        ).

    Inductive simpl_fun (f : X -> E) : Prop :=
        | decomposition :
            ∀ l : list ((X -> Prop) * E),
            simpl_fun_for l f
            -> simpl_fun f.

End simpl_fun_def.

Lemma Forall_map :
    forall A B : Type, forall f : A -> B, forall P : A -> Prop, forall Q : B -> Prop,
        (forall a : A, P a -> Q (f a)) -> forall l : list A, List.Forall P l -> List.Forall Q (List.map f l).
Proof.
    move => A B f P Q H l.
    induction l.
    simpl; trivial.
    simpl.
    move => LFP.
    pose tl := (List.map f l).
    apply List.Forall_cons.
    apply List.Forall_inv in LFP.
    auto.
    apply List.Forall_inv_tail in LFP.
    auto.
Qed.

Section simpl_fun_norm.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context (μ : measure gen).

    Open Scope R_scope.

    Definition fun_norm (f : X -> E) :=
        fun x => norm (f x).

    Lemma fun_norm_simpl_for : ∀ f : X -> E, ∀ l : list ((X -> Prop) * E),
        simpl_fun_for μ l f -> 
        simpl_fun_for μ (List.map (fun c => (fst c, norm (snd c))) l) (fun_norm f).
    Proof.
        move => f l l_is_dec.
        
        pose lnorm := List.map (fun c => (fst c, norm (snd c))) l.
        assert ((List.map fst lnorm) = (List.map fst l)) as Hl.
            clear l_is_dec μ gen.
            unfold lnorm; clear lnorm.
            induction l => //.
            simpl; congr cons; auto.


        split.
            (* lnorm est une décomposition bien formée *)
            rewrite Hl.
            case: l_is_dec => well_formed_l _ => //.
            (* et fun_norm f coïncide bien avec la décomposition donnée par lnorm *)
            case: l_is_dec => _ [case_in case_out].
            split => x.
            pose Pl :=
                fun c : ((X -> Prop) * E) => 
                    let (P, v) := c in
                    P x -> f x = v.
            apply (Forall_map _ _ (fun c => (fst c, norm (snd c))) Pl).
                move => [P v]; unfold Pl => Hf => /= Px.
                unfold fun_norm; congr norm; auto.
                case: (case_in x); auto.

            move => Hlnorm.
        
            assert 
                (List.Forall 
                (λ c : (X → Prop) * E, 
                    let (P, _) := c in
                    ¬ P x) l) as Subgoal.
                clear case_in case_out Hl μ gen; move: Hlnorm; unfold lnorm; clear lnorm.
                induction l => //.
                move: IHl; case: a => [P v] IHl H.
                pose Hhead := List.Forall_inv H; clearbody Hhead.
                pose Htail := List.Forall_inv_tail H; clearbody Htail; clear H.
                simpl in Hhead, Htail.
                apply List.Forall_cons => //; auto.
                assert (f x = zero) as fnul.
                    apply case_out => //.
                replace (zero) with 0 at 1. 2 : by compute.
                unfold fun_norm; rewrite fnul.
                apply norm_zero.
    Qed.

    Lemma fun_norm_simpl : ∀ f : X -> E,
        simpl_fun μ f -> simpl_fun μ (fun_norm f).
    Proof.
        move => f.
        case => l /fun_norm_simpl_for Hl.
        Print decomposition.
        apply (@decomposition X _ R_NormedModule gen μ (fun_norm f)
            (List.map (λ c : (X → Prop) * E, (fst c, norm (snd c))) l)).
        exact Hl.
    Defined.

    Close Scope R_scope.

End simpl_fun_norm.

Section simpl_fun_prop.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context (μ : measure gen).

    Open Scope list_scope.

    Fixpoint sf_of_list (l : list ((X -> Prop) * E)) : X -> E :=
        match l return X -> E with
            | nil => fun _ => zero
            | (P, v) :: tail =>
                fun x =>
                    match (excluded_middle_informative (P x)) return E with
                        | left _ => v
                        | right _ => sf_of_list tail x
                    end
        end.

    Remove Printing If sumbool.

    Lemma sf_sf_of_list : 
        ∀ l : list ((X -> Prop) * E), 
            well_formed_decomposition μ (List.map fst l) ->
            simpl_fun_for μ l (sf_of_list l).
    Proof.
        induction l => //=.
            (* cas <> nil *)
            case: a => [P v] wf_lext.
            pose wf_l := well_formed_tail μ wf_lext; clearbody wf_l.
            move: wf_l => /IHl => {}IHl.
            case: IHl. move => wf_l [case_in case_out].
            split => //; split => x.
            {
                apply List.Forall_cons.
                move => Px.
                pose H := (left (¬ P x) Px).
                case (excluded_middle_informative (P x)) => //.

                case (excluded_middle_informative (P x)) => //.
                move => Px.
                clear case_out case_in wf_l.
                case: wf_lext => Disj _.
                case: (Disj x) => /=.
                    move => H; pose Abs := List.Forall_inv H => //.
                    move => U. inversion U.
                        clear H0 H H1 tail x0 U Disj Px P.
                        move: H2.
                        induction l => //=.
                        case: a => [P w] => /= HPl.
                        pose Hhead := List.Forall_inv HPl; clearbody Hhead.
                        pose Htail := List.Forall_inv_tail HPl; clearbody Htail; clear HPl.
                        simpl in Hhead.
                        apply List.Forall_cons => //.
                        apply IHl => //.

                        apply False_ind => //.
            }{
                move => H.
                pose Hhead := List.Forall_inv H; clearbody Hhead.
                pose Htail := List.Forall_inv_tail H; clearbody Htail; clear H.
                simpl in Hhead.
                case: (excluded_middle_informative (P x)) => //.
                move => _. auto.
            }
    Qed.

    Definition fun_plus (f g : X -> E) :=
        fun x => plus (f x) (g x).

    Definition adapted_list_sf_sum (lf lg : list ((X -> Prop) * E)) 
        : list ((X -> Prop) * E) :=
        let Outlf := fun x : X => 
            (List.Forall 
            (fun c : (X -> Prop) * E => ¬ (fst c) x) 
            lf)
        in
        let Outlg := fun x : X => 
            (List.Forall 
            (fun c : (X -> Prop) * E => ¬ (fst c) x) 
            lg) 
        in
        let decomp_on_lg := fun c : (X -> Prop) * E =>
            let (P, v) := c in
            (fun x => P x ∧ Outlg x, v) ::
            (List.map (fun c' : (X -> Prop) * E =>
                let (Q, w) := c' in
                (fun x => P x ∧ Q x, plus v w)) 
            lg)
        in
        (List.map 
            (fun c : (X -> Prop) * E =>
            let (Q, w) := c in
            (fun x => Outlf x ∧ Q x, w))
        lg) ++
        (List.flat_map decomp_on_lg lf).

    Section simpl_fun_sum.
        
        Lemma lem1 : 
            ∀ (lf lg : list ((X → Prop) * E)) (f g : X → E),
                simpl_fun_for μ lf f
                → simpl_fun_for μ lg g
                → disjoint (List.map fst (adapted_list_sf_sum lf lg)).
        Proof.
            move => lf lg f g [wf_lf _] [wf_lg _].
            clear f g; move: wf_lf wf_lg; move: lf lg.
            induction lf.
                (* cas où lf est la liste nil *)
                move => lg _ Hlg.
                unfold adapted_list_sf_sum => /=.
                rewrite List.app_nil_r.
                move: Hlg; move: lg.
                induction lg.
                    (* cas lg nil *)
                    case; easy.
                    (* cas où lg <> nil *)
                    case: a => [Q w].
                    simpl => Hlgext x.
                    pose Hlg := IHlg (well_formed_tail μ Hlgext); clearbody Hlg.
                    case: (Hlg x); clear Hlg IHlg => Hlg.
                    case: (excluded_middle_informative (Q x)).
                        move => Qx; right.
                        apply Unique_base_case.
                            easy.
                            assumption.
                        move => NQx; left.
                        apply List.Forall_cons => //.
                        easy.
                    right.
                    unfold well_formed_decomposition in Hlgext.
                    case: Hlgext => Disj_lgext _.
                    unfold disjoint in Disj_lgext.
                    assert (¬ Q x) as NQx.
                    case: (Disj_lgext x); clear Disj_lgext.
                        apply List.Forall_inv.
                        move => U; inversion U; clear H H0 U tail x0 H1.
                        apply False_ind.
                        assert 
                            (List.Forall (λ y : X → Prop, ¬ y x)
                                (List.map fst
                                    (List.map
                                        (λ c : (X → Prop) * E,
                                            let (Q, w) := c in
                                            (λ x : X, List.Forall (λ c0 : (X → Prop) * E, ¬ fst c0 x) nil ∧
                                             Q x, w)) lg))
                            )
                            as Absurdity.
                            clear Q w Hlg.
                            pose lg1 := (List.map fst lg).
                            assert (lg1 = (List.map fst lg)); unfold lg1. 
                                reflexivity.
                            fold lg1 in H2.
                            Check List.Forall_rect.
                            clearbody lg1; move: H; move: lg; move: H2; move: lg1.
                            pose P_to_prove := 
                                (
                                    fun lg1 => ∀ lg : list ((X → Prop) * E),
                                        lg1 = List.map fst lg
                                        → List.Forall (λ y : X → Prop, ¬ y x)
                                            (List.map fst
                                            (List.map
                                                (λ c : (X → Prop) * E,
                                                    let (Q, w) := c in
                                                    (λ x0 : X, List.Forall (λ c0 : (X → Prop) * E, ¬ fst c0 x0) nil ∧ Q x0,
                                                     w)) lg))
                                ).
                            apply (@List.Forall_ind _ (λ y : X → Prop, ¬ y x) P_to_prove).
                                unfold P_to_prove => lg Hlg.
                                assert (lg = nil) as nillg.
                                    move: Hlg.
                                    induction lg => //.
                                rewrite nillg => //=.
                                move => Q lg1 NQx Hlg1.
                                unfold P_to_prove => IHlg1 lg Eqlg1.
                                case_eq lg => //=.

        Admitted.

        Lemma lem2 :
            ∀ (lf lg : list ((X → Prop) * E)) (f g : X → E),
                simpl_fun_for μ lf f
                → simpl_fun_for μ lg g
                → List.Forall (measurable gen) (List.map fst (adapted_list_sf_sum lf lg)).
        Admitted.

        Lemma lem3 :
            ∀ (lf lg : list ((X → Prop) * E)) (f g : X → E),
                simpl_fun_for μ lf f
                → simpl_fun_for μ lg g
                → List.Forall (finite_measured μ)
                    (List.map fst (adapted_list_sf_sum lf lg)).
        Admitted.

        Lemma lem4 :
            ∀ (lf lg : list ((X → Prop) * E)) (f g : X → E),
                simpl_fun_for μ lf f
                → simpl_fun_for μ lg g
                → ∀ x : X,
                    List.Forall
                        (λ c : (X → Prop) * E, let (P, v) := c in P x → fun_plus f g x = v)
                        (adapted_list_sf_sum lf lg).
        Admitted.

        Lemma lem5 :
            ∀ (lf lg : list ((X → Prop) * E)) (f g : X → E),
                simpl_fun_for μ lf f
                → simpl_fun_for μ lg g
                → ∀ x : X,
                    List.Forall (λ c : (X → Prop) * E, let (P, _) := c in ¬ P x)
                        (adapted_list_sf_sum lf lg) → fun_plus f g x = zero.
        Admitted.

    End simpl_fun_sum.
    
    Lemma simpl_fun_sum :
        ∀ f g : X -> E, ∀ lf lg : list ((X -> Prop) * E),
            simpl_fun_for μ lf f -> simpl_fun_for μ lg g 
            -> simpl_fun_for μ (adapted_list_sf_sum lf lg) (fun_plus f g).
    Proof.
        move => f g lf lg Hf Hg.
        repeat split.
        all : move: Hf Hg.
        all : move: f g.
        all : move: lf lg.

        exact lem1.
        exact lem2.
        exact lem3.
        exact lem4.
        exact lem5.
    Qed.

    (*

        move => f g lf lg; move: f g. move: lf lg.
        induction lf; induction lg.

            (* cas des listes nil *)
            move => f g 
                [wf_lf [_ case_out_lf]]
                [wf_lg [_ case_out_lg]].
            repeat split => //.
            unfold adapted_list_sf_sum => //=.
            move => x _.
            assert (List.Forall (λ c : (X → Prop) * E, let (P, _) := c in ¬ P x) nil) as nilForall by easy.
            pose fxnul := case_out_lf x nilForall; clearbody fxnul.
            pose gxnul := case_out_lg x nilForall; clearbody gxnul.
            unfold fun_plus; rewrite fxnul gxnul plus_zero_l => //.

            (* Cas de la liste lg non nulle *)
            case: a => [Q w] f g 
                [wf_lf [case_in_lf case_out_lf]]
                [wf_lgext [case_in_lgext case_out_lgext]].
            split.
                unfold well_formed_decomposition; split.
                unfold well_formed_decomposition in wf_lgext.
                case: wf_lgext => Disj _.
                
            assert (simpl_fun_for μ nil f) as f_sf_nil
                by unfold simpl_fun_for => //.
            clear case_in_lf wf_lf.
            assert (∀ x : X, List.Forall (λ c : (X → Prop) * E, let (P, _) := c in ¬ P x) nil) as nilForall by easy.
            assert (∀ x : X, f x = zero) as fnul.
                move => x. apply case_out_lf => //.
            clear case_out_lf nilForall.
            
            pose wf_lg := well_formed_tail μ wf_lgext; clearbody wf_lg.
            replace ((fix map (l : list ((X → Prop) * E)) : list (X → Prop) :=
                    match l with
                        | nil => nil
                        | a :: t => fst a :: map t
                    end) lg)
                with (List.map fst lg) in wf_lg at 1 => //.
            
            pose h := sf_of_list lg.
            pose Hh := sf_sf_of_list lg wf_lg; clearbody Hh; fold h in Hh.
            pose Hfh := IHlg f h f_sf_nil Hh; clearbody Hfh.
            clear Hh f_sf_nil.
            unfold simpl_fun_for.
            split.
                unfold adapted_list_sf_sum => /=.
                rewrite List.app_nil_r.
                assert 
                    (
                        (List.map
                            (λ c : (X → Prop) * E,
                                let (Q, w) := c in
                                (λ x : X,
                                    List.Forall (λ c0 : (X → Prop) * E, ¬ fst c0 x) nil ∧ Q x,
                                w)) lg)
                        = adapted_list_sf_sum nil lg
                    ) as Expr.
                    unfold adapted_list_sf_sum => /=.
                    rewrite List.app_nil_r; reflexivity.
                rewrite Expr; clear Expr.
                case: wf_lgext.
            unfold adapted_list_sf_sum => /=; rewrite List.app_nil_r.
            assert (List.Forall (λ c : (X → Prop) * E, let (P, _) := c in ¬ P x) nil) as nilForall by easy.
            pose fxnul := case_out_lf x nilForall; clearbody fxnul.
            unfold simpl_fun_for; repeat split => /=.

                (* 1 : le support est disjoint *)
    
    *)
                
    (*

    Definition sf_plus (f_sf g_sf : { h : X -> E | simpl_fun μ h }) :=
        match (f_sf, g_sf) with
            (exist f π, exist g π)

    Definition SimplFunAbelianGroup_mixin : AbelianGroup.mixin_of { f : X -> E | simpl_fun μ f }.
        eapply (AbelianGroup.Mixin { f : X -> E | simpl_fun μ f } plus).

    *)

End simpl_fun_prop.

*)

(* 

Une troisième tentative !

*)

Section simpl_fun_def.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context (E : NormedModule A).

    Definition indic (P : X -> Prop) : X -> A :=
        fun x =>
            match (excluded_middle_informative (P x)) return A with
                | left _ => one
                | right _ => zero
            end.

    Open Scope core_scope.
    Open Scope type_scope.
    Close Scope R_scope.
    
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context (μ : measure gen).

    (* la fonction est val ∘ which *)
    Record simpl_fun := mk_simpl_fun {
        (* where peut renvoyer une valeur plus grande que max_where
        dans ce cas, val renvoie une valeur nulle *)
        which : X -> nat;
        val : nat -> E;
        max_which : nat;

        ax_max_which :
            ∀ n : nat, n >= max_which -> val n = zero;
        ax_mesurable :
            ∀ n : nat, n < max_which ->
                measurable gen (fun x => which x = n);
        ax_finite :
            ∀ n : nat, n < max_which ->
                is_finite (μ (fun x => which x = n))
    }.

    Definition nth_carrier (sf : simpl_fun) (n : nat) : (X -> Prop) :=
        (fun x => sf.(which) x = n).

    Definition fun_sf (sf : simpl_fun) : X -> E :=
        fun x => sf.(val) (sf.(which) x).

    Definition is_simpl (f : X -> E) :=
        ∃ sf : simpl_fun, ∀ x : X, fun_sf sf x = f x.

End simpl_fun_def.

Section simpl_fun_norm.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context (E : NormedModule A).
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context (μ : measure gen).

    Open Scope R_scope.
    Open Scope nat_scope.

    Definition fun_norm (f : X -> E) :=
        fun x => norm (f x).

    Definition simpl_fun_norm_aux (sf : simpl_fun E μ) : simpl_fun R_NormedModule μ.
        case: sf => which val max_which ax1 ax2 ax3.
        pose nval :=
            fun n => norm (val n).
        apply (mk_simpl_fun R_NormedModule μ which nval max_which).
            (* ax_max_which *)
            move => n Hn; unfold nval.
            rewrite ax1.
            apply norm_zero.
            assumption.
            (* ax_mesurable *)
            exact ax2.
            (* ax_finite *)
            exact ax3.
    Defined.

    Lemma simpl_fun_norm :
        ∀ f : X -> E, is_simpl E μ f -> 
            is_simpl R_NormedModule μ (fun_norm f).
    Proof.
        move => f.
        case => sf. case_eq sf => which val max_which ax1 ax2 ax3 Eqsf Eqf.
        exists (simpl_fun_norm_aux sf).
        rewrite Eqsf.
        move => x; unfold fun_sf, simpl_fun_norm_aux => /=.
        simpl in Eqf.
        rewrite Eqf => //.
    Qed.

End simpl_fun_norm.