From stdpp Require Import list.
From Nominal Require Export Atom Group.

Notation perm := (list (name * name)).

Definition swap '(a,b) : name -> name :=
  λ c, if decide (a = c) then b else if decide (b = c) then a else c.

Definition perm_action (p: perm): name -> name := 
  λ a, foldl (λ x y, swap y x) a p.

(* Swap & perm properties *)
Lemma swap_id (a x: name): swap (a,a) x = x.
Proof. simpl; case_decide; congruence. Qed.

Lemma swap_involutive a x: swap a (swap a x) = x.
Proof. destruct a; simpl; repeat case_decide; congruence. Qed.

Lemma perm_action_app p q x: perm_action (p ++ q) x = perm_action q (perm_action p x).
Proof. unfold perm_action. rewrite foldl_app; simpl; auto. Qed.

Lemma perm_action_left_rev p : forall x, perm_action (reverse p) (perm_action p x) = x.
Proof with auto.
  induction p; intros.
  - simpl...
  - assert (HH1: ∀ a, a :: p = [a] ++ p)...
    (* rewrite HH1, reverse_app, reverse_singleton. *)
    rewrite HH1, reverse_app, reverse_singleton, <-perm_action_app, <-app_assoc, 3?perm_action_app;
      simpl; rewrite IHp, swap_involutive...
Qed.

Lemma perm_action_right_rev p x: perm_action p (perm_action (reverse p) x) = x.
Proof with auto.
  induction p(* ; intros. *).
  - simpl...
  - assert (HH1: ∀ a, a :: p = [a] ++ p)...
    rewrite HH1, reverse_app, reverse_singleton, <-perm_action_app, <-app_assoc, 3?perm_action_app;
      simpl; rewrite swap_involutive...
Qed.

(** *Permutation group  *)
#[global] Instance perm_neutral: Neutral perm := @nil (name * name).
#[global] Instance perm_operator: Operator perm := @app (name * name).
#[global] Instance perm_inverse: Inverse perm := @reverse (name * name).
#[global] Instance perm_equiv: Equiv perm :=
  λ p q: perm, ∀ a: name, perm_action p a = perm_action q a.
#[global] Instance perm_equivalence: Equivalence (≡@{perm}).
Proof. repeat split; repeat intro; [symmetry | etransitivity]; eauto. Qed.

#[global] Instance PermGrp: Group perm.
Proof with auto.
  split; unfold op, perm_operator, neutral, perm_neutral, inv, perm_inverse,
         equiv, perm_equiv in *; repeat intro...
  - typeclasses eauto.
  - rewrite 2?perm_action_app; do 2 match goal with H : context[_ = _] |- _ => rewrite H end...
  - transitivity (perm_action (reverse y) (perm_action x (perm_action (reverse x) a)));
    [rewrite H, perm_action_left_rev | rewrite perm_action_right_rev]...
  - rewrite app_assoc...
  - rewrite app_nil_r...
  - rewrite perm_action_app, perm_action_right_rev...
  - rewrite perm_action_app, perm_action_left_rev...
Qed.

Section PermGroupProperties.
  Lemma swap_equiv_neutral (a : name): [(a,a)] ≡@{perm} ɛ.
  Proof. unfold equiv, perm_equiv, perm_action; intros; simpl; case_decide; auto. Qed.

  Lemma swap_expand (a c b: name):
    c ≠ a -> c ≠ b -> [(a,c)] ≡@{perm} [(a,b)] + [(b,c)] + [(a,b)].
  Proof.
    intros; unfold equiv, perm_equiv, perm_action; intros; simpl; repeat case_decide; subst; congruence.
  Qed.
  
End PermGroupProperties.

(** *Permtutation Types *)

(* Permutation action *)
Class PAct X := pact :> Action perm X.
#[global] Hint Mode PAct ! : typeclass_instances.
(* Instance: Params (@pact) 1 := {}. *)

Class Perm (X : Type) `{PA : PAct X, Equiv X} : Prop := {
  ptype :> GAction PermGrp X (Act := @pact X PA)
}.

(* Section PermType.
  Context (X : Type) `{PA: PAct X, Equiv X}.

  Class Perm : Prop := 
    ptype :> GAction perm X (Act := @pact X PA).
End PermType.
 *)
 #[global] Hint Mode Perm ! - - : typeclass_instances.

(* Class Perm X `{XA: PermAction X, Equiv X} : Prop :=
  perm_type :> GAction perm X XA.
#[global] Hint Mode Perm - - - : typeclass_instances. *)

(* Permutation types properties *)
(* Section PermTypeProperties.
  Context `{Perm X}.

  
End PermTypeProperties.
 *)
(* (** *Equivariant functions  *)
Class EquivarF A B := equivar: A -> B.
#[global] Hint Mode EquivarF ! ! : typeclass_instances.
Infix "~>" := EquivarF (at level 90, right associativity).

Class Equivariant (A B: Type) `{Perm A, Perm B, A ~> B} := {
  equivar_proper :> Proper ((≡@{A}) ==> (≡@{B})) equivar;
  equivariance : forall (p : perm) (a: A), p ∙ (equivar a) ≡@{B} equivar (p ∙ a)
}.
 *)

(* Perm Instances *)
(* Perm *)
#[global] Instance perm_act_conj : PAct perm := λ p q, (-p) + (q + p).
#[global, refine] Instance PermPerm: Perm perm := { ptype := _ }. 
Proof.
  split; intros; unfold action, pact, perm_act_conj, "+", perm_operator.
  - typeclasses eauto.
  - repeat intro; pose proof H as Hn; apply group_inv_inj in Hn; unfold "≡", perm_equiv in *;
        rewrite 4!perm_action_app, H, H0, Hn; reflexivity.
  - unfold ɛ, perm_neutral; simpl; rewrite app_nil_r; auto.
  - unfold "- _", perm_inverse; rewrite reverse_app, <-2!app_assoc, app_assoc; auto.   
Qed. 
