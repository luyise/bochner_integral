
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
*)

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
        ∃ x : R, (μ P) = Finite x.

    Definition well_formed_decomposition (l : list (X -> Prop)) : Prop :=
        disjoint l ∧ 
        List.Forall (measurable gen) l ∧
        List.Forall (finite_measured) l.

    Definition simpl_fun_for (l : list ((X -> Prop) * E)) (f : X -> E) :=
        well_formed_decomposition (List.map fst l) ∧
        (List.Forall
            (fun (c : (X -> Prop) * E) => 
                let (P, v) := c in
                ∀ x : X, P x -> f x = v
            )
            l
        )
        ∧
        ∀ x : X, 
            (List.Forall
                (fun (c : (X -> Prop) * E) =>
                    let (P, v) := c in
                    ¬ P x
                )
                l
            -> f x = zero).

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

        assert (simpl_fun_for μ lnorm (fun_norm f)) as Goal.
            split.
            (* lnorm est une décomposition bien formée *)
            rewrite Hl.
            case: l_is_dec => well_formed_l _ => //.
            (* et fun_norm f coïncide bien avec la décomposition donnée par lnorm *)
            case: l_is_dec => _ l_describe_f.
            unfold lnorm.
            split.
            pose Pl :=
                fun c : ((X -> Prop) * E) => 
                    let (P, v) := c in
                    ∀ x : X, P x -> f x = v.
            apply (Forall_map _ _ (fun c => (fst c, norm (snd c))) Pl).
                move => [P v]; unfold Pl => Hf x => /= Px.
                unfold fun_norm; congr norm; auto.
                case: l_describe_f => //.
            case: l_describe_f => [_ Hlzero].
            move => x.
            fold lnorm => Hlnorm.
            assert 
                (List.Forall 
                (λ c : (X → Prop) * E, 
                    let (P, _) := c in
                    ¬ P x) l) as Subgoal.
                clear Hlzero Hl f μ gen; move: Hlnorm; unfold lnorm; clear lnorm.
                induction l => //; case: a => [P v].
                simpl. move => H.
                pose Hhead := List.Forall_inv H; clearbody Hhead.
                pose Htail := List.Forall_inv_tail H; clearbody Htail; clear H.
                simpl in Hhead.
                apply List.Forall_cons => //; auto.
                assert (f x = zero) as fnul.
                    apply Hlzero => //.
                replace (zero) with 0 at 1. 2 : by compute.
                unfold fun_norm; rewrite fnul.
                apply norm_zero.
        
        fold lnorm; assumption.
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

End simpl_fun_norm.