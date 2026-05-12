-- Random practice with equalities, quantifiers, and tactics
example (α : Type) : α → α := by
  intro h
  exact h

example (α : Type) : ∀ x : α, x = x := by
  intro h
  rfl

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro n1 n2 n3 eq eq2
  exact Eq.trans (Eq.symm eq2) eq

example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro h
  exact Exists.elim h (fun x hOr =>
    Or.elim hOr
    (fun hp => Exists.intro x (Or.intro_right (q x) hp))
    (fun hq => Exists.intro x (Or.intro_left (p x) hq)))

example (x y z w : Nat) (h1 : x = y) (h2 : y = z) (h3 : z = w) : x = w := by
  apply Eq.trans h1
  apply Eq.trans h2
  exact h3

example : ∀ x y z w : Nat, x = y → y = z → z = w → x = w := by
  intros h1 h2 h3 h4 h5 h6 h7
  apply Eq.trans h5
  apply Eq.trans h6
  apply h7

example (x : Nat) : x = x := by
  revert x
  intro x; rfl

example (x y : Nat) (h : x = y) : y = x := by
  apply (Eq.symm h)

example : 3 = 3 := by
  generalize 3 = x
  rfl

example : 2 + 3 = 5 := by
  generalize h : 3 = x
  rw [← h]

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  · apply Or.inr
    assumption
  · apply Or.inl
    assumption

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption

example (p : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp

inductive Goblin where
| hobgoblin : Goblin
| shaman : Goblin
| rider : Goblin
