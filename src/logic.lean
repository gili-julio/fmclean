
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro pboom,
  exact pboom(p),
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro bbp,
  by_cases p : P,
  exact p,
  exfalso,
  exact bbp(p),
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro bbp,
  by_cases p : P,
  exact p,
  exfalso,
  exact bbp(p),
  intro p,
  intro pb,
  exact pb(p),
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro poq,
  cases poq with p q,
  right,
  exact p,
  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro peq,
  split,
  exact peq.right,
  exact peq.left,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro pboq,
  intro p,
  cases pboq with pb q,
  exfalso,
  exact pb(p),
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro poq,
  intro pb,
  cases poq with p q,
  exfalso,
  exact pb(p),
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro ptq,
  intro qb,
  intro p,
  have q : Q := ptq(p),
  exact qb(q),
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro qbtpb,
  intro p,
  by_cases q : Q,
  exact q,
  have pb : ¬P := qbtpb(q),
  exfalso,
  exact pb(p),
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro ptq,
  intro qb,
  intro p,
  have q : Q := ptq(p),
  exact qb(q),
  intro qbtpb,
  intro p,
  by_cases q : Q,
  exact q,
  have pb : ¬P := qbtpb(q),
  exfalso,
  exact pb(p),
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro popbb,
  apply popbb,
  right,
  intro p,
  apply popbb,
  left,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro ptqtp,
  intro pb,
  apply pb,
  apply ptqtp,
  intro p,
  exfalso,
  exact pb(p),
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro poq,
  intro pbeqb,
  cases poq with p q,
  apply pbeqb.left,
  exact p,
  apply pbeqb.right,
  exact q,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro peq,
  intro pboqb,
  cases pboqb with pb qb,
  apply pb,
  exact peq.left,
  apply qb,
  exact peq.right,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro poqb,
  split,
  intro p,
  apply poqb,
  left,
  exact p,
  intro q,
  apply poqb,
  right,
  exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro pbeqb,
  intro poq,
  cases poq with p q,
  apply pbeqb.left,
  exact p,
  apply pbeqb.right,
  exact q,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro peqb,
  by_cases p : P,
  left,
  intro q,
  apply peqb,
  split,
  exact p,
  exact q,
  right,
  exact p,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro qbopb,
  intro peq,
  cases qbopb with qb pb,
  apply qb,
  exact peq.right,
  apply pb,
  exact peq.left,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro peqb,
  by_cases p : P,
  left,
  intro q,
  apply peqb,
  split,
  exact p,
  exact q,
  right,
  exact p,
  intro qbopb,
  intro peq,
  cases qbopb with qb pb,
  apply qb,
  exact peq.right,
  apply pb,
  exact peq.left,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro poqb,
  split,
  intro p,
  apply poqb,
  left,
  exact p,
  intro q,
  apply poqb,
  right,
  exact q,
  intro pbeqb,
  intro poq,
  cases poq with p q,
  apply pbeqb.left,
  exact p,
  apply pbeqb.right,
  exact q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro peqor,
  have p : P := peqor.left,
  have qor : Q ∨ R := peqor.right,
  cases qor with q r,
  left,
  split,
  exact p,
  exact q,
  right,
  split,
  exact p,
  exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro peqoper,
  cases peqoper with peq per,
  split,
  exact peq.left,
  left,
  exact peq.right,
  split,
  exact per.left,
  right,
  exact per.right,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro poqer,
  cases poqer with p qer,
  split,
  left,
  exact p,
  left,
  exact p,
  split,
  right,
  exact qer.left,
  right,
  exact qer.right,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro poqepor,
  cases poqepor with poq por,
  cases poq with p q,
  left,
  exact p,
  cases por with p r,
  left,
  exact p,
  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro peqtr,
  intro p,
  intro q,
  apply peqtr,
  split,
  exact p,
  exact q,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro ptqtr,
  intro peq,
  apply ptqtr,
  exact peq.left,
  exact peq.right,
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
  intro peq,
  exact peq.left,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro peq,
  exact peq.right,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pep,
  exact pep.left,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro pop,
  cases pop with p p,
  exact p,
  exact p,
  intro p,
  left,
  exact p,
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
  sorry,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
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
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
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
