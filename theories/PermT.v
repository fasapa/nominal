From Nominal Require Export Group Swap Permutation.
Open Scope nominal_scope.

(** *Permutation as list forms a Group *)
#[export] Instance perm_neutral: Neutral perm := @nil (name * name).
#[export] Instance perm_operator: Operator perm := @app (name * name).
#[export] Instance perm_inverse: Inverse perm := @reverse (name * name).
#[export] Instance perm_equiv: Equiv perm :=
  λ p q: perm, ∀ a: name, perm_swap p a = perm_swap q a.
#[export] Instance perm_equivalence: Equivalence (≡@{perm}).
Proof. repeat split; repeat intro; [symmetry | etransitivity]; eauto. Qed.

#[export] Instance PermGrp: Group perm.
Proof with auto.
  split; unfold op, perm_operator, neutral, perm_neutral, inv, perm_inverse,
         equiv, perm_equiv in *; repeat intro...
  - typeclasses eauto.
  - rewrite 2?perm_swap_app; do 2 match goal with H : context[_ = _] |- _ => rewrite H end...
  - transitivity (perm_swap (reverse y) (perm_swap x (perm_swap (reverse x) a)));
    [rewrite H, perm_swap_left_rev | rewrite perm_swap_right_rev]...
  - rewrite app_assoc...
  - rewrite app_nil_r...
  - rewrite perm_swap_app, perm_swap_right_rev...
  - rewrite perm_swap_app, perm_swap_left_rev...
Qed.

(* PermGroup Properties *)
Lemma perm_equiv_neutral a: ⟨a,a⟩ ≡@{perm} ɛ.
Proof. unfold equiv, perm_equiv, perm_swap; intros; simpl; case_decide; auto. Qed.

Lemma perm_expand (a b c: name):
  c ≠ a -> c ≠ b -> ⟨a,c⟩ ≡@{perm} ⟨a,b⟩ + ⟨b,c⟩ + ⟨a,b⟩.
Proof.
  intros; unfold equiv, perm_equiv, perm_swap; intros; simpl; 
    repeat case_decide; subst; congruence.
Qed.

Lemma swap_perm a b: ⟨a,b⟩ ≡@{perm} ⟨b,a⟩.
Proof. 
  unfold equiv, perm_equiv, perm_swap; intros; simpl; 
    repeat case_decide; subst; auto.
Qed.

Lemma perm_duplicate a b: ⟨a,b⟩ + ⟨a,b⟩ ≡@{perm} ɛ.
Proof.
  unfold equiv, perm_equiv, perm_swap; intros; simpl;
    repeat case_decide; subst; first [congruence | auto].
Qed.

Lemma perm_inv a b: ⟨a,b⟩ ≡@{perm} -⟨a,b⟩.
Proof. unfold equiv, perm_equiv, inv, perm_inverse; simpl; intros; repeat (case_decide); auto. Qed.

Lemma perm_comm_distr a b p: ⟨a,b⟩ + p ≡ p + ⟨perm_swap p a, perm_swap p b⟩.
Proof.
  unfold equiv, perm_equiv, op, perm_operator; intros x;
  destruct (decide (a = x)), (decide (b = x)); subst; rewrite 2!perm_swap_app.
  - rewrite 2!perm_equiv_neutral; auto.
  - rewrite 2!perm_swap_left; auto.
  - rewrite 2!perm_swap_right; auto. 
  - rewrite 2!perm_swap_neither; try apply perm_swap_neq; intuition.
Qed.

Lemma perm_notin_dom_comm a b p: 
  a ∉ perm_dom p → b ∉ perm_dom p → ⟨a,b⟩ + p ≡@{perm} p + ⟨a,b⟩.
Proof.
  intros; rewrite perm_comm_distr; unfold equiv, perm_equiv; intros x;
    rewrite 2!(perm_notin_domain_id p); auto.
Qed.

Lemma perm_dom_inv p a: a ∉ perm_dom p → a ∉ perm_dom (-p).
Proof. 
  induction p as [| p p' IHp]; intros H.
  - simpl in *; auto.
  - assert (HH: ∀ A (x: A) y, x :: y = [x] ++ y). { intros; simpl; auto. }
    unfold inv, perm_inverse; rewrite reverse_cons; rewrite HH in H.
    rewrite perm_dom_concat in *; set_solver.
Qed.

(* Permutation Type *)
Class PermAction X := action: perm → X → X.
#[export] Hint Mode PermAction ! : typeclass_instances.

(* CAUSA PROBLEMAS COM REESCRITA ENVOLVENDO action (- p)
  Instance: Params (@action) 2 := {}. *)

Infix "•" := action (at level 60, right associativity): nominal_scope.
Notation "(•)" := action (only parsing): nominal_scope.
Notation "(• x )" := (action x) (only parsing): nominal_scope.
Notation "( x •)" := (λ y, action y x) (only parsing): nominal_scope.

(* Permutation type is a type with a permutation group (left) action *)
Class PermT (X : Type) `{Act: PermAction X, Equiv X}: Prop := {
  gact_setoid :> Equivalence(≡@{X});
  gact_proper :> Proper ((≡@{perm}) ⟹ (≡@{X}) ⟹ (≡@{X})) (•);

  gact_id: ∀ (x: X), ɛ • x ≡@{X} x;
  gact_compat: ∀ (p q: perm) (x: X), p • (q • x) ≡@{X} (q + p) • x
}.

#[export] Hint Mode PermT ! - - : typeclass_instances.
#[export] Existing Instance gact_setoid.
#[export] Existing Instance gact_proper.

(* Arguments gact_id {_ _ _ _ _ Grp _ _ _ GAct} : rename.
Arguments gact_compat {_ _ _ _ _ Grp _ _ _ GAct} : rename.
Arguments gact_proper {_ _ _ _ _ Grp _ _ _ GAct} : rename. *)

Section PermTypeProperties.
  Context `{PermT X}.

  Corollary perm_left_inv (x: X) p: (-p) • p • x ≡ x.
  Proof. rewrite gact_compat, grp_right_inv, gact_id; auto. Qed.

  Corollary perm_rigth_inv (x: X) p: p • (-p) • x ≡ x.
  Proof. rewrite gact_compat, grp_left_inv, gact_id; auto. Qed.

  Lemma perm_iff (x y: X) p: p • x ≡ y ↔ x ≡ (-p) • y.
  Proof. split; intros A; 
    [rewrite <-A, perm_left_inv | rewrite A, perm_rigth_inv]; auto.
  Qed.

  Lemma perm_inj (x y: X) p: p • x ≡ p • y ↔ x ≡ y.
  Proof. split; intros A; 
    [apply perm_iff in A; rewrite <-(perm_left_inv y p) | rewrite A]; auto.
  Qed.

  Lemma perm_inv_empty_act (x: X): (-ɛ) • x ≡ x.
  Proof. rewrite grp_inv_neutral; apply gact_id. Qed.

  Lemma perm_action_duplicate a b (x: X): ⟨a,b⟩ • ⟨a,b⟩ • x ≡ x.
  Proof. rewrite gact_compat, perm_duplicate; apply gact_id. Qed.

  Lemma perm_action_equal a (x: X): ⟨a,a⟩ • x ≡ x.
  Proof. rewrite perm_equiv_neutral; apply gact_id. Qed.

  Lemma perm_comm a b p (x: X): a ∉ perm_dom p → b ∉ perm_dom p → ⟨a,b⟩ • p • x ≡ p • ⟨a,b⟩ • x.
  Proof. intros; rewrite gact_compat, <-perm_notin_dom_comm, <-gact_compat; auto. Qed.

  Lemma perm_swap_distr a b p (x: X): p • ⟨a,b⟩ • x ≡ ⟨perm_swap p a, perm_swap p b⟩ • p • x.
  Proof. rewrite 2gact_compat, perm_comm_distr; auto. Qed.
End PermTypeProperties.

(* #[global] Instance action_perm_proper `{Perm A}: Proper ((≡@{perm}) ⟹ (≡@{A}) ⟹ (≡@{A})) action.
Proof. apply gact_proper. Qed. *)