
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro pb,
  have b:false := pb p,
  exact b,
  
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro p,
  by_contradiction,
  apply p,
  intro a,
  exact h(a),

end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro p,
  by_contradiction,
  exact p(h),
  intro q,
  intro r,
  exact r(q),

end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro p,
  cases p with j hj,
  right,
  exact j,
  left,
  exact hj,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro p,
  cases p with a b,
  split,
  exact b,
  exact a,

end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro p,
  intro q,
  cases p with a b,
  exfalso,
  exact a(q),
  exact b, 
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros p q,
  cases p with a b,
  exfalso,
  exact q(a),
  exact b,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros p q r,
  have k := p(r),
  exact q(k), 
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros p q,
  by_contradiction,
  have j := p(h),
  exact j(q),
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intros p q r,
  have k := p(r),
  exact q(k),
  intros l i,
  by_contradiction,
  have u := l(h),
  exact u(i),
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro p,
  exfalso,
  apply p,
  right,
  intro q,
  apply p,
  left,
  exact q,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
 intro p,

 
  
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros p q,
  cases q with a b,
  cases p with j k,
  exact a(j),
  exact b(k),
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros p q,
  cases p with a b,
  cases q with j k,
  exact j(a),
  exact k(b),
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro p,
  split,
  intro q,
  apply p,
  left,
  exact q,
  intro j,
  apply p,
  right,
  exact j,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros p q,
  cases p with a b,
  cases q with j k,
  exact a(j),
  exact b(k),

end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro p,
  left,
  intro q,
  apply p,
  split,
  exfalso,

end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros p q,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  sorry,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro p,
  cases p with a b,
  cases b with j k,
  left,
  split,
  exact a,
  exact j,
  right,
  split,
  exact a,
  exact k,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro p,
  cases p with a b,
  cases a with j k,
  
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro p,
  split,
  cases p with a b,
  left,
  exact a,
  cases b with j k,
  right,
  exact j,
  cases p with h i,
  left,
  exact h,
  cases i with v u,
  right,
  exact u,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro p,
  cases p with a b,
  cases a with j k,
  left,
  exact j,
  cases b with h i,
  left,
  exact h,
  right,
  split,
  exact k,
  exact i,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  ,

end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros p q,
  cases q with a b,
  have k := p(a),
  have j := k(b),
  exact j,
  
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro p,
  cases p with a b,
  exact a,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro p,
  cases p with a b,
  exact b,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro p,
  cases p with a,
  exact a,
  intro p,
  split,
  repeat{exact p,},

end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro p,
  cases p with a,
  exact a,
  exact p,
  intro q,
  right,
  exact q,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro p,
  by_contradiction,
  cases p with a ha,
  have k := h(a),
  exact k(ha),
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  ,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro p,
  split,
  cases p with a ha,
  existsi a,
  cases ha with j k,
  exact j,
  cases p with b hb,
  existsi b,
  cases hb with u v,
  exact v,


end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro p,
  cases p with a ha,
  cases ha with j k,
  left,
  existsi a,
  exact j,
  right,
  existsi a,
  exact k,

end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro p,
  cases p with j k,
  cases j with a ha,
  existsi a,
  left,
  exact ha,
  cases k with b hb,
  existsi b,
  right,
  exact hb,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro p,
  split,
  intro a,
  have k := p(a),
  cases k with h i,
  exact h,
  intro b,
  have j := p(b),
  cases j with u v,
  exact v,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro p,
  cases p with j k,
  intro a,
  split,
  have r := j(a),
  exact r,
  have s := k(a),
  exact s,
  
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro p,
  intro a,
  cases p with j k,
  left,
  have h := j(a),
  exact h,
  have i := k(a),
  right,
  exact i,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
