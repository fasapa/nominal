From Nominal Require Export Name.

Definition Swap: Type := (Name * Name).

Definition swap '(a,b): Name → Name :=
  λ c, if decide (a = c) then b else if decide (b = c) then a else c.

Notation "⟨ a , b ⟩" := (@cons Swap (a,b) nil).

Section SwapProperties.
  Context (a b c d: Name).

  Lemma swap_left: swap (a,b) a = b.
  Proof. simpl; repeat case_decide; congruence. Qed.

  Lemma swap_right: swap (a,b) b = a.
  Proof. simpl; repeat case_decide; congruence. Qed.

  Lemma swap_neither1: a ≠ c → b ≠ c → swap (a, b) c = c.
  Proof. intros; simpl; repeat case_decide; congruence. Qed.

  Lemma swap_neither2: swap (a, b) c = c → (a ≠ c ∧ b ≠ c) ∨ (a = c ∧ b = c).
  Proof. 
    intros; simpl in *; try repeat case_decide; subst;
        [right | congruence | left]; auto.
  Qed.

  Lemma swap_neq: a ≠ b → swap (c, d) a ≠ swap (c, d) b.
  Proof. intros; simpl; repeat case_decide; congruence. Qed.

  Lemma swap_id: swap (a,a) c = c.
  Proof. simpl; case_decide; congruence. Qed.

  Lemma swap_involutive p: swap p (swap p a) = a.
  Proof. destruct p; simpl; repeat case_decide; congruence. Qed.
End SwapProperties.

