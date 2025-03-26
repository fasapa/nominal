From Coq Require Import Bool.Sumbool.
From stdpp Require Import boolset decidable.
From Nominal Require Export Lambda.
From Nominal.Instances Require Import Bool.

Lemma reflect_false_iff: ∀ (P: Prop) (b: bool), reflect P b → ¬P ↔ b = false.
Proof. intros ? ? H; inversion H; split; intros; congruence. Qed.

Notation ℙᴰ P X := (∀ x: X, Decision (P x)) (only parsing).

Notation "{[ x | P ]}" := (BoolSet (λ x, P)) (at level 1, x as pattern, format "{[ x | P ]}") : stdpp_scope.

Definition boolean_respectfull `{Equiv X} (x y: X) (B: X → bool) := x ≡ y → B x = B y.
Definition prop_respectfull_iff `{Equiv X} (x y: X) (P: X → Prop) := x ≡ y → (P x ↔ P y).
(* αCompat *)

Section PropNominal.
    Context (X: Type).

    Section Pbool.
        Context `{Hdec: ℙᴰ P X}.
        
        Definition ℙB (x: X): bool.
            elim (decide (P x)); intros; [exact true | exact false].
        Defined.

        Lemma propdec_reflect_true_iff (x: X): P x ↔ ℙB x = true.
        Proof. split; intros; unfold ℙB,sumbool_rec,sumbool_rect in *; case_decide; first [congruence | auto]. Qed.
    
        Lemma propdec_reflect_false_iff (x: X): ¬(P x) ↔ ℙB x = false.
        Proof. split; intros; unfold ℙB,sumbool_rec,sumbool_rect in *; case_decide; first [congruence | auto]. Qed.

        Lemma propdec_reflect_b (x: X): reflect (P x) (ℙB x).
        Proof. destruct (Hdec x) as [p | n].
            - rewrite (proj1 (propdec_reflect_true_iff x) $ p); constructor; auto.
            - rewrite (proj1 (propdec_reflect_false_iff x) $ n); constructor; auto.
        Qed.
    End Pbool.

    Section RespectFullReflect.
    Context `{EX: Equiv X, @Equivalence X (@equiv X EX)} (Pp: X → Prop) (Pb: X → bool) 
             (R: ∀ x: X, reflect (Pp x) (Pb x)).

        Lemma boolean_prop_respectfull_right (x y: X): 
            boolean_respectfull x y Pb → prop_respectfull_iff x y Pp.
        Proof. split; intros HH; unfold boolean_respectfull,prop_respectfull_iff in *.
            - apply (reflect_iff _ _ (R _)); rewrite <-H0; [apply (reflect_iff _ _ (R _)) |]; assumption.
            - apply (reflect_iff _ _ (R _)); rewrite H0; [apply (reflect_iff _ _ (R _)) |]; assumption.
        Qed.

        Lemma boolean_prop_respectfull_left (x y: X): 
            prop_respectfull_iff x y Pp → boolean_respectfull x y Pb.
        Proof. unfold prop_respectfull_iff, boolean_respectfull in *; intros A B.
            pose proof R as R'; specialize (R x); specialize (R' y); destruct (Pb x) eqn: Bx; destruct (Pb y) eqn: By.
            - reflexivity.
            - specialize (A B) as [C D]. 
              rewrite <-Bx in R; apply reflect_iff in R; apply R in Bx.
              rewrite <-By in R'; apply reflect_false_iff in R'; apply R' in By; apply C in Bx;
              congruence.
            - specialize (A B) as [C D].
              rewrite <-Bx in R; apply reflect_false_iff in R; apply R in Bx.
              rewrite <-By in R'; apply reflect_iff in R'; apply R' in By; apply D in By; congruence.
            - reflexivity.
        Qed.

        Lemma boolean_prop_respectfull_right_iff (x y: X):
            boolean_respectfull x y Pb ↔ prop_respectfull_iff x y Pp.
        Proof. split; [apply boolean_prop_respectfull_right | apply boolean_prop_respectfull_left]. Qed.
    
    Section Boolsets.
        Context `{Nominal X}.
                
        (* There is already a reflection mechanism going on here. Is_true coerces bool into Prop for <-> *)
        Lemma elem_of_BoolSet (B: X → bool) x: B x ↔ x ∈ {[ x | B x ]}.
        Proof. done. Qed.
        
        Lemma not_elem_of_BoolSet (B: X → bool) x: ¬B x ↔ x ∉ {[ x | B x ]}.
        Proof. done. Qed.

        Definition boolset_act (p: Perm) (BS: boolset X): boolset X := {[ x | (p • boolset_car BS) x ]}.
        #[export] Instance BoolsetAction: PermAction (boolset X) := boolset_act.

        Coercion boolset_car: boolset >-> Funclass.

        (* Since booleans forms a discrete nominal set, so we have *)
        Lemma bool_predicate_discrete (B: X → bool) (p: Perm) (x: X): 
            (p • B) x = B (-p • x). (* instead of p • (B (-p • x)) *)
        Proof. reflexivity. Qed.

        (* The same is true for boolsets *)
        Lemma boolset_act_discrete (BS: boolset X) (p: Perm) (x: X): boolset_act p BS = {[ x | BS (-p • x) ]}.
        Proof. reflexivity. Qed.
        
        Lemma boolset_act_discrete_iff (BS: boolset X) (p: Perm) (x: X): (p • BS) x ↔ -p • x ∈ BS.
        Proof. split; intros; assumption. Qed.
     
        (* Characterisation of the set (p • BS) 
           p • BS ≜ { p • x | x ∈ BS } *)

        Lemma perm_boolset_in_iff_inv (BS: boolset X) (p: Perm) (x: X): x ∈ (p • BS) ↔ -p • x ∈ BS.
        Proof. split; intros HH; apply HH. Qed.

        Hypothesis (bscar_respect_equiv: ∀ (x y: X) (BS: boolset X), boolean_respectfull x y BS).

        Instance: Proper ((≡@{X}) ==> eq ==> impl) (@elem_of X (boolset X) boolset_elem_of).
        Proof. repeat intro; subst; unfold "∈",boolset_elem_of in *; rewrite (bscar_respect_equiv y x y0); auto. Qed.

        Instance: Proper ((≡@{X}) ==> eq ==> flip impl) (@elem_of X (boolset X) boolset_elem_of).
        Proof. repeat intro; subst; unfold "∈",boolset_elem_of in *; rewrite (bscar_respect_equiv x y y0); auto. Qed.
     
        (* These two next lemmas can only be proved if we show that elem_of is proper in relation to the equivalence of X.
           To show it, we need to assume that the characteristic boolean function from the boolset also
           respects the equivalence of X. From the point of view of the reflection, this is the same as the
           αCompatibility proposed by Copello. *)
        Lemma inv_perm_boolset_iff_exists (BS: boolset X) (p: Perm) (x: X): -p • x ∈ BS ↔ ∃ x', x' ∈ BS ∧ x ≡ p • x'.
        Proof. 
            split; intros.
            - exists (- p • x); split; [auto | rewrite perm_rigth_inv]; reflexivity.
            - destruct H2 as [x' [? H3]]. rewrite H3,perm_left_inv; assumption.
        Qed.

        Lemma perm_boolset_in_boolset_iff (BS: boolset X) (p: Perm) (x: X): (p • x) ∈ (p • BS) ↔ x ∈ BS.
        Proof.
            split; intros HH.
            - pose proof (perm_boolset_in_iff_inv BS p (p • x)) as [H2].
              apply H2 in HH. rewrite perm_left_inv in HH. auto.
            - apply perm_boolset_in_iff_inv. rewrite perm_left_inv. auto.
        Qed.
    End Boolsets.

    Section PropDecBoolsets.
        Context `(Hdec: ℙᴰ P X) `{Nominal X}.

        Definition Pᵇ: boolset X := BoolSet (@ℙB P Hdec).
        
        Lemma boolset_prop_true_iff (x: X): x ∈ Pᵇ ↔ P x.
        Proof. split; intros HH;
            [apply propdec_reflect_true_iff, Is_true_true | 
             apply propdec_reflect_true_iff, Is_true_true in HH]; auto. 
        Qed.
        
        Lemma boolset_prop_false_iff (x: X): x ∉ Pᵇ ↔ ¬(P x).
        Proof. split; intros HH;
            [apply propdec_reflect_false_iff, Is_true_false |
             apply propdec_reflect_false_iff, Is_true_false in HH]; auto.
        Qed.

        Lemma perm_in_boolset_iff_prop_perm (x: X) (p: Perm): x ∈ (p • Pᵇ) ↔ P (-p • x).
        Proof.
            split; intros.
            - pose proof perm_boolset_in_boolset_iff. 
            
            pose proof (act_spec3 π P x) as []. apply H2 in H1.
              apply lele. assumption.
            - pose proof (act_spec3 π P x) as []. apply H3. apply lele. assumption.
        Qed.

    End PropDecBoolsets.
        
    Lemma hehe (x: X) (π: Perm): x ∈ (π • P) ↔ ℙ (-π • x).
    Proof.
        split; intros.
        - pose proof (act_spec3 π P x) as []. apply H2 in H1.
          apply lele. assumption.
        - pose proof (act_spec3 π P x) as []. apply H3. apply lele. assumption.
    Qed.
    





End PropNominal.

(* Section PropBool.
    Context {X: Type} `{H: PredicateDec X P}.

    (* Turn a decidable predicate into a function returning boolean *)
    Definition B (x: X): bool.
        elim (decide (P x)); intros; [exact true | exact false].
    Defined.
    
    Lemma reflect_true_iff (x: X): P x ↔ B x = true.
    Proof.
        split; intros A.
        - unfold B,sumbool_rec,sumbool_rect; case_decide; auto.
        - unfold B,sumbool_rec,sumbool_rect in A; case_decide; congruence.
    Qed.
    
    Lemma reflect_false_iff (x: X): ¬(P x) ↔ B x = false.
    Proof.
        split; intros A.
        - unfold B,sumbool_rec,sumbool_rect; case_decide; congruence.
        - unfold B,sumbool_rec,sumbool_rect in A; case_decide; congruence.
    Qed.
End PropBool. *)

Section PSets.
    Context `{Nominal X}.
    Hypothesis (boolean_respectfull: ∀ (x y: X) (s: X → bool), x ≡ y → s x = s y).
    (* αCompat: x ≡ y → P x ↔ P y *)
    (*          x ≡ y → p x = true ↔ p y = true  *)
    (*          x ≡ y → p x = p y *)

    Coercion boolset_car: boolset >-> Funclass.

    Instance: Proper ((≡@{X}) ==> eq ==> flip impl) (@elem_of X (boolset X) boolset_elem_of).
    Proof.
        repeat intro; subst. unfold "∈",boolset_elem_of in *;
        rewrite (boolean_respectfull x y y0); auto.
    Qed.

    Lemma elem_of_BoolSet (P: X → bool) x : x ∈ {[ x | P x ]} ↔ P x.
    Proof. done. Qed.
        
    Lemma not_elem_of_BoolSet (P: X → bool) x : x ∉ {[ x | P x ]} ↔ ¬P x.
    Proof. done. Qed.

    Lemma bool_predicate_discrete (π: Perm) (p: X → bool) (x: X): 
        (π • p) x = p (-π • x).
    Proof. reflexivity. Qed.

    Definition act (g: Perm) (S: boolset X): boolset X :=
        {[ x | (g • boolset_car S) x ]}.

    Instance BoolsetAction: PermAction (boolset X) := act.

    Lemma act_spec0 (g: Perm) (S: boolset X): act g S = {[ x | S (-g • x) ]}.
    Proof. reflexivity. Qed.
        
    Lemma act_spec1 (g: Perm) (S: boolset X) (x: X): 
        (g • S) x ↔ -g • x ∈ S.
    Proof. split; intros; assumption. Qed.

    Lemma act_spec2 (g: Perm) (S: boolset X) (x: X): 
        -g • x ∈ S ↔ ∃ x', x' ∈ S ∧ x ≡ g • x'.
    Proof. 
        split; intros.
        - exists (- g • x); split; [auto | rewrite perm_rigth_inv]; reflexivity.
        - destruct H1 as [x' []]. rewrite H2,perm_left_inv; assumption.
    Qed.

    (* g • S ≜ { g • x | x ∈ S } *)

    Lemma act_spec3 (g: Perm) (S: boolset X) (x: X): 
        x ∈ (g • S) ↔ -g • x ∈ S.
    Proof. split; intros HH; apply HH. Qed.

    Lemma act_spec4 (g: Perm) (S: boolset X) (x: X):
        (g • x) ∈ (g • S) ↔ x ∈ S.
    Proof.
        split; intros HH.
        - pose proof (act_spec3 g S (g • x)) as [].
          apply H1 in HH. rewrite perm_left_inv in HH. auto.
        - apply act_spec3. rewrite perm_left_inv. auto.
    Qed.

    Context (ℙ: X → Prop) (P: boolset X).
    Hypothesis (Hr: ∀ x: X, reflect (ℙ x) (P x)).
    
    Lemma LALA (G: X → bool) x : x ∈ {[ x | G x ]} → G x = true.
    Proof. intros. unfold elem_of,boolset_elem_of in H1; simpl in *; apply Is_true_eq_true. assumption. Qed.

    Lemma LULU (G: X → bool) x : x ∉ {[ x | G x ]} → G x = false.
    Proof. intros. unfold elem_of,boolset_elem_of in H1; simpl in *; apply Is_true_false_1; assumption. Qed.

    Lemma lele (x: X): x ∈ P ↔ ℙ x.
    Proof.
        split; intros; specialize (Hr x).
        - apply reflect_iff in Hr; apply Hr. apply elem_of_BoolSet,LALA in H1. assumption.
        - apply reflect_iff in Hr. apply Hr in H1. apply elem_of_BoolSet. destruct P; simpl in *.
          apply Is_true_true_2; assumption.
    Qed.

    Lemma lulu (x: X): x ∉ P ↔ ¬ ℙ x.
    Proof.
        split; intros; specialize (Hr x).
        - apply reflect_iff in Hr. intro. apply not_elem_of_BoolSet in H1. simpl in *.
          apply LULU in H1. apply Hr in H2. congruence.
        - apply reflect_iff in Hr. intro. apply H1. apply LALA in H2. apply Hr. assumption.
    Qed.
        
    Lemma hehe (x: X) (π: Perm): x ∈ (π • P) ↔ ℙ (-π • x).
    Proof.
        split; intros.
        - pose proof (act_spec3 π P x) as []. apply H2 in H1.
          apply lele. assumption.
        - pose proof (act_spec3 π P x) as []. apply H3. apply lele. assumption.
    Qed.

    Hypothesis (prop_compat1: ∀ (x y: X) (Q: X → Prop), x ≡ y → Q x → Q y).

    Instance: Proper (equiv ==> impl) ℙ.
    Proof. repeat intro. specialize (prop_compat1 x y ℙ H1). auto. Qed.

    Instance: Proper (equiv ==> flip impl) ℙ.
    Proof. repeat intro. symmetry in H1. specialize (prop_compat1 y x ℙ H1). auto. Qed.
    
    Lemma huhu (x: X) (π: Perm): (π • x) ∈ (π • P) ↔ ℙ x.
    Proof. split; intros.
        - apply lele. pose proof (act_spec4 π P x) as []. apply H2. assumption.
        - apply lele. rewrite perm_left_inv. assumption.
    Qed.
End PSets.

Section Props.
    Context (X: Type) `{Nominal X}.
    
    (* Decidibilidade *)
    Record Props := mkProps {
      prop_car :> X → Prop;
      prop_compat: ∀ (x y: X), x ≡ y → prop_car x → prop_car y;
      (* prop_support *)
    }.
End Props.

Section LOL.
    Context `{Nominal X}.

    Print Instances Equiv.

    Instance props_equiv: Equiv (Props X) := 
        fun (a b: Props X) => ∀ x, (prop_car X a x) ↔ (prop_car X b x).

    Instance props_equiv_equivalence: Equivalence props_equiv.
    Proof. split.
        - repeat intro. auto.
        - repeat intro; unfold props_equiv in H1; split.
            + intros. apply H1; auto.
            + intros. apply H1. auto.
        - repeat intro; unfold props_equiv in H1,H2; split.
            + intros. apply H2,H1; auto.
            + intros. apply H1,H2; auto.
    Qed.

    #[refine] Instance: PermAction (Props X) :=
    fun (p: Perm) (prop: Props X) => mkProps X _ (fun (a: X) => _).
    - exact (fun x => prop_car X prop (-p • x)).
    - intros; simpl in *. pose proof (prop_compat X prop (- p • a) (- p • y)).
      pose proof (@perm_inj X Act H (nperm X) a y (-p)) as [].
      apply H5 in H1. apply H3 in H1. assumption. assumption.
    Defined.

    Instance: PermT (Props X).
    Proof. split.
        - apply props_equiv_equivalence.
        - repeat intro; split; intro.
            + unfold equiv,props_equiv in H2. unfold action,PermAction_instance_0 in *; simpl in *.
              apply H2. apply (prop_compat X x0 (- x • x1) (- y • x1)).
              * rewrite H1; reflexivity.
              * assumption.
            + unfold equiv,props_equiv in H2. unfold action,PermAction_instance_0 in *; simpl in *.
              apply H2. apply (prop_compat X y0 (- y • x1) (- x • x1)).
              * rewrite <-H1. reflexivity.
              * assumption.
        - intros; unfold action,PermAction_instance_0,equiv,props_equiv; simpl; intros; split.
            + intros; pose proof (prop_compat X x (- ɛ • x0) x0). apply H2.
                * apply perm_inv_empty_act.
                * assumption.
            + intros; pose proof (prop_compat X x x0 (- ɛ • x0)); apply H2.
                * symmetry; apply perm_inv_empty_act.
                * assumption.
        - intros; unfold action,PermAction_instance_0,equiv,props_equiv; simpl; intros; split.
            + intros. pose proof (prop_compat X x (- q • - p • x0) (- (q + p) • x0)); apply H2.
                * rewrite perm_op_inv, gact_compat; reflexivity.
                * assumption.
            + intros. pose proof (prop_compat X x (- (q + p) • x0) (- q • - p • x0)); apply H2.
                * rewrite perm_op_inv, gact_compat; reflexivity.
                * assumption.
    Qed.

    Lemma eiseis (Q: Props X) (π: Perm) (x: X):
        (π • Q) x ↔ Q (-π • x).
    Proof. split; intro; simpl in *; assumption. Qed. 
        
    (* g • S ≜ { g • x | x ∈ S } *)
    Lemma oiois (Q: Props X) (π: Perm) (x: X): (π • Q) (π • x) ↔ Q x.
    Proof.
        split; intros.
        - pose proof (eiseis Q π (π • x)) as []. apply H2 in H1.
          apply (prop_compat X Q (- π • π • x)).
          + apply perm_left_inv.
          + assumption.
        - unfold action at 1; unfold PermAction_instance_0; simpl.
          apply (prop_compat X Q x).
          * symmetry. apply perm_left_inv.
          * assumption.
    Qed.

End LOL.

Instance: PermAction (Props X)



Section PowerSets.
    Context `{Nominal X, PredicateDec X P}.

    

    

    Definition PSet := BoolSet (@B _ P _).

    


    Check PSet.

    Definition ℙ: boolset X := {[ x | @B _ P _ x ]}.

    Definition act (g: Perm) (S: boolset X): boolset X :=
        {[ x | (g • boolset_car S) x ]}.

End PowerSets.

Section PowerSets.
    Context `{Nominal X}.

    Definition ℙ (P: X → bool) := {[ x | P x ]}.

    Definition ℙtop := ℙ (λ _, true). Definition ℙbot := ℙ (λ _, false).

    Example full_set: ∀ x: X, x ∈ ℙtop.
    Proof. intros; done. Qed.

    Example empty_set: ∀ x: X, x ∉ ℙbot.
    Proof. intros; apply not_elem_of_BoolSet; auto. Qed.

    Lemma boolset_discrete (π: Perm) (p: X → bool) (x: X): 
        (π • p) x = p (-π • x). 
    Proof. reflexivity. Qed.

    Definition act (g: Perm) (S: boolset X): boolset X :=
        {[ x | (g • boolset_car S) x ]}.

    Lemma act1 (g: Perm) (S: boolset X): act g S = {[ x | S (-g • x) ]}.
    Proof. reflexivity. Qed.

    Lemma act2 (g: Perm) (S: boolset X) (x: X): (g • boolset_car S) x ↔ -g • x ∈ S.
    Proof. split; intros; assumption. Qed.

    Check boolset_car.

    Instance boolset_proper (s: boolset X): Proper (equiv ==> eq) (boolset_car s).
    Admitted.

    Instance LALA: Proper ((≡@{X}) ==> eq ==> flip impl) (@elem_of X (boolset X) boolset_elem_of).
    Proof. repeat intro; subst. unfold "∈",boolset_elem_of in *. rewrite H1. assumption. Qed.
    
    Lemma act3 (g: Perm) (S: boolset X) (x: X): 
        -g • x ∈ S ↔ ∃ x', x' ∈ S ∧ x ≡ g • x'.
    Proof. split; intros.
        - exists (- g • x); split; [auto | rewrite perm_rigth_inv]; reflexivity.
        - destruct H1 as [x' []]. rewrite H2. 

    

    Set Printing All.
    Print act1.

    Instance bool_action: PermAction (boolset X) := 
        fun π s => {[ x | (π • s) x ]}.

End PowerSets.




Definition ℙ := Λ → bool.

Definition S (P: ℙ) := {[ x | P x ]}.

Lemma boolset_discrete (π: Perm) (p: ℙ) (x: Λ): (π • p) x = p (-π • x). 
Proof. unfold action at 1; unfold fun_action; unfold action at 1; unfold bool_action; reflexivity. Qed.

Lemma lol (π: Perm) (p: ℙ) (x: Λ):
    (π • p) x ↔ -π • x ∈ (@S p).
Proof. split; intros.
    - apply elem_of_BoolSet; rewrite <-boolset_discrete; assumption.
    - rewrite boolset_discrete. assumption.
Qed.



(* Definition ℙ := Λ → bool.
Definition inℙ (t: Λ) (P: ℙ) := P t = true.
Definition ninℙ (t: Λ) (P: ℙ) := P t = false.  *)

(* Notation " x 'in' P " := (inℙ x P) (at level 100).
Notation " x 'not_in' P " := (ninℙ x P) (at level 100). *)

Lemma ℙ_action_iff (π: Perm) (p: ℙ) (x: Λ): 
    (π • p) x = true ↔ inℙ (-π • x) p.
Proof. split; intros.
    - unfold action, fun_action in H; unfold action at 1 in H; unfold bool_action in H.
      apply Is_true_eq_true; assumption.
    - unfold action, fun_action; unfold action at 1; unfold bool_action.
      apply Is_true_eq_left; assumption. 
Qed. 

Check ℙ_action_iff.

Lemma lol: ∀ (π: Perm) (S: ℙₛ), π • S ≡ S.
Proof.
    unfold equiv,fun_supp_equiv. 
    Proof. unfold equiv,fun_supp_equiv; intros; rewrite fsupp_action.
        unfold action at 1; unfold bool_action. reflexivity.
    Qed.

Check reflect.

Section Test.
    Context (t: Λ) (P: Λ → Prop) (P_dec: decidable (P t)).

    Check sumboolP P_dec.
    Check sameP.

    

End Test.