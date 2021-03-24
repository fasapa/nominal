From Nominal Require Export Prelude.

(** *Group operations *)
Class Neutral A := neutral : A.
Hint Mode Neutral ! : typeclass_instances.
Notation ε := neutral.

Class Operator A := op: A → A → A.
Hint Mode Operator ! : typeclass_instances.
(* Instance: Params (@op) 2 := {}. *)
Infix "+" := op : nominal_scope.
Notation "(+)" := op (only parsing) : nominal_scope.
Notation "(+ x )" := (op x) (only parsing) : nominal_scope.
Notation "( x +)" := (λ y, op y x) (only parsing) : nominal_scope.

Class Inverse A := inv : A → A.
Hint Mode Inverse ! : typeclass_instances.
(* Instance: Params (@inv) 1 := {}. *)
Notation "- x" := (inv x) : nominal_scope.
Notation "(-)" := inv (only parsing) : nominal_scope.
Notation "x - y" := (x + (-y))%nom (only parsing) : nominal_scope.

Section Group.
  Context A `{Equiv A, !Equivalence(≡@{A}), Neutral A, Operator A, Inverse A}.

  Class Group: Prop := {
    group_assoc : ∀ x y z, x + (y + z) ≡@{A} (x + y) + z;
    group_left_id : ∀ x, ε + x ≡@{A} x;
    group_right_id : ∀ x, x + ε ≡@{A} x;
    group_left_inv : ∀ x, (-x) + x ≡@{A} ε;
    group_right_inv : ∀ x, x - x ≡@{A} ε;

    group_setoid :> Equivalence(≡@{A});
    group_op_proper :> Proper ((≡@{A}) ==> (≡@{A}) ==> (≡@{A})) (+);
    group_inv_proper :> Proper ((≡@{A}) ==> (≡@{A})) (-)
  }.
End Group.

Arguments group_assoc {A AEq NA OA IA GA}: rename.
Arguments group_left_id {A AEq NA OA IA GA}: rename.
Arguments group_right_id {A AEq NA OA IA GA}: rename.
Arguments group_left_inv {A AEq NA OA IA GA}: rename.
Arguments group_right_inv {A AEq NA OA IA GA}: rename.
Arguments group_op_proper {A AEq NA OA IA GA}: rename.
Arguments group_inv_proper {A AEq NA OA IA GA}: rename.

Section GroupProperties.
  Context `{Group G}.

  Corollary group_inv_involutive (x: G): x ≡ --x.
  Proof with auto.
    rewrite <-group_left_id at 1; rewrite <-group_left_inv, <-group_assoc, group_left_inv, group_right_id;
      reflexivity.
  Qed.

  Corollary inv_neutral: ε ≡@{G} -ε.
  Proof with auto.
    rewrite <-group_left_inv at 2; rewrite group_right_id, <-group_inv_involutive...
  Qed.

  (* Corollary group_inv_inj (x y: G): x ≡ y → (-x) ≡ (-y). *)
  (* Proof. apply group_inv_proper. Qed. *)
End GroupProperties.

(** *Group action *)
Class Action `(Group A) X := action: A → X → X.
(* Instance: Params (@action) 2 := {}. *)
Infix "∙" := action (at level 60, right associativity) : nominal_scope.
Notation "(∙)" := action (only parsing) : nominal_scope.
Notation "(∙ x )" := (action x) (only parsing) : nominal_scope.
Notation "( x ∙)" := (λ y, action y x) (only parsing): nominal_scope.

Section GroupAction.
  Context A X `{Action A X, Equiv X, !Equivalence(≡@{X})}.

  Class GroupAction: Prop := {
    action_id : ∀ (x: X), ε ∙ x ≡@{X} x;
    action_compat: ∀ (p q: A) (r: X), p ∙ (q ∙ r) ≡@{X} (q + p) ∙ r;

    (* action_group :> Group A; *)
    action_setoid :> Equivalence(≡@{X});
    action_proper :> Proper ((≡@{A}) ==> (≡@{X}) ==> (≡@{X})) (∙)
  }.
End GroupAction.

Arguments action_compat {A X AEq NA OA IA GA ActAX XEq GActAX}: rename.
Arguments action_id {A X AEq NA OA IA GA ActAX XEq GActAX}: rename.
Arguments action_proper {A X AEq NA OA IA GA ActAX XEq GActAX}: rename.
