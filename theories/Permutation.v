From stdpp Require Export list.
From Nominal Require Export Group Swap.
Open Scope nominal_scope.

(* Permutation is just a list of pair of names. *)
Notation Perm := (list Swap).

Definition perm_swap (p: Perm): Name → Name := 
  λ a, foldl (λ x y, swap y x) a p.

(* Properties *)
Lemma perm_swap_app (r s: Perm) a: perm_swap (r ++ s) a = perm_swap s (perm_swap r a).
Proof. unfold perm_swap; rewrite foldl_app; simpl; auto. Qed.

Lemma perm_swap_left_rev (p: Perm): ∀ a, perm_swap (reverse p) (perm_swap p a) = a.
Proof with auto.
  assert (HH: ∀ {A} (x: A) y, x :: y = [x] ++ y)... induction p; intros.
  - simpl...
  - rewrite HH, reverse_app, reverse_singleton, <-perm_swap_app, <-app_assoc,
      3?perm_swap_app; simpl; rewrite IHp; apply swap_involutive.
Qed.

Lemma perm_swap_right_rev (p : Perm) a: perm_swap p (perm_swap (reverse p) a) = a.
Proof with auto.
  assert (HH: ∀ {A} (x: A) y, x :: y = [x] ++ y)... induction p.
  - simpl...
  - rewrite HH, reverse_app, reverse_singleton, <- perm_swap_app, <-app_assoc, 
      3?perm_swap_app; simpl; rewrite swap_involutive...
Qed.

Lemma perm_swap_neither (a b c: Name): a ≠ b → a ≠ c → perm_swap ⟨b,c⟩ a = a.
Proof. unfold perm_swap, foldl; intros; rewrite swap_neither1; intuition. Qed.

Lemma perm_swap_left (a b: Name): perm_swap ⟨a,b⟩ a = b.
Proof. unfold perm_swap, foldl; apply swap_left. Qed.

Lemma perm_swap_right (a b: Name): perm_swap ⟨b,a⟩ a = b.
Proof. unfold perm_swap, foldl. apply swap_right. Qed.

Lemma perm_swap_neq p: ∀ a b, a ≠ b → perm_swap p a ≠ perm_swap p b.
Proof. induction p as [|[] ? IHp]; [| intros; simpl; apply IHp,swap_neq]; auto. Qed.

(* Permutation domain *)
Fixpoint perm_dom (p: Perm): NameSet :=  
  match p with
  | [] => ∅
  | (a,b) :: p' => {[a; b]} ∪ perm_dom p'
  end.

(* Proof depends on listset_empty implementation. TODO: alternative? *)
Lemma perm_dom_concat p: ∀ p', perm_dom (p ++ p') = (perm_dom p) ∪ (perm_dom p').
Proof.
Transparent listset_empty.
  induction p.
  - intros; simpl; unfold empty, listset_empty, union, listset_union; simpl;
      destruct (perm_dom p'); reflexivity.
  - intros; simpl; destruct a as [a b]; rewrite IHp, assoc; auto.
    unfold Assoc, union, listset_union; intros [] [] []; rewrite assoc; [auto | typeclasses eauto].
Opaque listset_empty.
Qed.

Lemma perm_notin_domain_id (p: Perm) (a: Name): a ∉ (perm_dom p) → perm_swap p a = a.
Proof.
  intros; induction p as [| [b c] p'].
  - reflexivity.
  - assert (HH: ∀ A (x: A) y, x :: y = [x] ++ y). { reflexivity. }
    rewrite HH, perm_swap_app; simpl in H; do 2 apply not_elem_of_union in H as [H ?];
    rewrite perm_swap_neither; set_solver.
Qed.

(** *Permutation as list forms a Group *)
#[export] Instance perm_neutral: Neutral Perm := @nil Swap.
#[export] Instance perm_operator: Operator Perm := @app Swap.
#[export] Instance perm_inverse: Inverse Perm := @reverse Swap.
#[export] Instance perm_equiv: Equiv Perm :=
  λ p q: Perm, ∀ a: Name, perm_swap p a = perm_swap q a.
#[export] Instance perm_equivalence: Equivalence (≡@{Perm}).
Proof. repeat split; repeat intro; [symmetry | etransitivity]; eauto. Qed.

#[export] Instance PermGrp: Group Perm.
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
Lemma perm_equiv_neutral a: ⟨a,a⟩ ≡@{Perm} ɛ.
Proof. unfold equiv, perm_equiv, perm_swap; intros; simpl; case_decide; auto. Qed.

Open Scope nominal_scope.

Lemma perm_expand (a b c: Name):
  c ≠ a -> c ≠ b -> ⟨a,c⟩ ≡@{Perm} ⟨a,b⟩ + ⟨b,c⟩ + ⟨a,b⟩.
Proof.
  intros; unfold equiv, perm_equiv, perm_swap; intros; simpl; 
    repeat case_decide; subst; congruence.
Qed.

Lemma swap_perm a b: ⟨a,b⟩ ≡@{Perm} ⟨b,a⟩.
Proof. 
  unfold equiv, perm_equiv, perm_swap; intros; simpl; 
    repeat case_decide; subst; auto.
Qed.

Lemma perm_duplicate a b: ⟨a,b⟩ + ⟨a,b⟩ ≡@{Perm} ɛ.
Proof.
  unfold equiv, perm_equiv, perm_swap; intros; simpl;
    repeat case_decide; subst; first [congruence | auto].
Qed.

Lemma perm_inv a b: ⟨a,b⟩ ≡@{Perm} -⟨a,b⟩.
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
  a ∉ perm_dom p → b ∉ perm_dom p → ⟨a,b⟩ + p ≡@{Perm} p + ⟨a,b⟩.
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