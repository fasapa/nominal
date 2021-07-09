From stdpp Require Import list.
From Nominal Require Export Atom Group.

(* Permutation is just a list of pair of names. *)
Notation perm := (list (name * name)).
Notation "⟨ a , b ⟩" := (@cons (name * name) (a,b) nil).

(* Swap action on pair *)
Definition swap '(a,b) : name → name :=
  λ c, if decide (a = c) then b else if decide (b = c) then a else c.

(* Swap on perm *)
Definition swap_perm (p: perm): name → name := 
  λ a, foldl (λ x y, swap y x) a p.

Section SwapProperties.
  Context (a b c : name) (p : name * name) (r s : perm).

  Lemma swap_left : swap (a,b) a = b.
  Proof. simpl; repeat case_decide; congruence. Qed.

  Lemma swap_right : swap (a,b) b = a.
  Proof. simpl; repeat case_decide; congruence. Qed.

  Lemma swap_neither : a ≠ c → b ≠ c → swap (a, b) c = c.
  Proof. intros; simpl; repeat case_decide; congruence. Qed.

  Lemma swap_id : swap (a,a) c = c.
  Proof. simpl; case_decide; congruence. Qed.

  Lemma swap_involutive : swap p (swap p a) = a.
  Proof. destruct p; simpl; repeat case_decide; congruence. Qed.

  Lemma swap_perm_app : swap_perm (r ++ s) a = swap_perm s (swap_perm r a).
  Proof. unfold swap_perm; rewrite foldl_app; simpl; auto. Qed.
End SwapProperties.

Lemma swap_perm_left_rev (p : perm) : ∀ a, swap_perm (reverse p) (swap_perm p a) = a.
Proof with auto.
  assert (HH: ∀ {A} (x: A) y, x :: y = [x] ++ y)... induction p; intros.
  - simpl...
  - rewrite HH, reverse_app, reverse_singleton, <-swap_perm_app, <-app_assoc,
      3?swap_perm_app; simpl; rewrite IHp; apply swap_involutive.
Qed.

Lemma swap_perm_right_rev (p : perm) a: swap_perm p (swap_perm (reverse p) a) = a.
Proof with auto.
  assert (HH: ∀ {A} (x: A) y, x :: y = [x] ++ y)... induction p.
  - simpl...
  - rewrite HH, reverse_app, reverse_singleton, <- swap_perm_app, <-app_assoc, 
      3?swap_perm_app; simpl; rewrite swap_involutive...
Qed.

(** *Permutation as list forms a Group *)
#[global] Instance perm_neutral: Neutral perm := @nil (name * name).
#[global] Instance perm_operator: Operator perm := @app (name * name).
#[global] Instance perm_inverse: Inverse perm := @reverse (name * name).
#[global] Instance perm_equiv: Equiv perm :=
  λ p q: perm, ∀ a: name, swap_perm p a = swap_perm q a.
#[global] Instance perm_equivalence: Equivalence (≡@{perm}).
Proof. repeat split; repeat intro; [symmetry | etransitivity]; eauto. Qed.

#[global] Instance PermGrp: Group perm.
Proof with auto.
  split; unfold op, perm_operator, neutral, perm_neutral, inv, perm_inverse,
         equiv, perm_equiv in *; repeat intro...
  - typeclasses eauto.
  - rewrite 2?swap_perm_app; do 2 match goal with H : context[_ = _] |- _ => rewrite H end...
  - transitivity (swap_perm (reverse y) (swap_perm x (swap_perm (reverse x) a)));
    [rewrite H, swap_perm_left_rev | rewrite swap_perm_right_rev]...
  - rewrite app_assoc...
  - rewrite app_nil_r...
  - rewrite swap_perm_app, swap_perm_right_rev...
  - rewrite swap_perm_app, swap_perm_left_rev...
Qed.

Section PermGroupProperties.
  Context (a b c : name).

  Lemma swap_equiv_neutral : ⟨a,a⟩ ≡ ɛ@{perm}.
  Proof. unfold equiv, perm_equiv, swap_perm; intros; simpl; case_decide; auto. Qed.

  Lemma swap_expand :
    c ≠ a -> c ≠ b -> ⟨a,c⟩ ≡@{perm} ⟨a,b⟩ + ⟨b,c⟩ + ⟨a,b⟩.
  Proof.
    intros; unfold equiv, perm_equiv, swap_perm; intros; simpl; 
      repeat case_decide; subst; congruence.
  Qed.
End PermGroupProperties.

(* Permutation action *)
Class PermAct X := prmact :> Action perm X.
#[global] Hint Mode PermAct ! : typeclass_instances.
(* Instance: Params (@pact) 1 := {}. *)

Polymorphic Class Perm (X : Type) `{P: PermAct X, Equiv X} := 
  prmtype :> GAction PermGrp X (Act := @prmact X P).
#[global] Hint Mode Perm ! - - : typeclass_instances.

#[global] Instance action_perm_proper `{Perm A}: Proper ((≡@{perm}) ⟹ (≡@{A}) ⟹ (≡@{A})) action.
Proof. apply gact_proper. Qed.