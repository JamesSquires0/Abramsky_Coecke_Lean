import Mathlib.Tactic

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     And.intro (And.right h) (And.left h))
    (fun h2 : q ∧ p =>
     And.intro (And.right h2) (And.left h2))

theorem or_swap {p q : Prop} (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      Or.intro_right q hp)
    (fun hq : q =>
      Or.intro_left p hq)

theorem or_swap_imp : p ∨ q → q ∨ p := by
  intro h
  exact Or.elim h
    (fun hp : p =>
      Or.intro_right q hp)
    (fun hq : q =>
      Or.intro_left p hq)

theorem or_equiv_swap : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (λ h : p ∨ q => or_swap h)
    (λ h2 : q ∨ p => or_swap h2)

-- SUPPORTING THM FOR ASSOC_OR_RIGHT
lemma assoc_or_right_sup {p q r : Prop} (h : p ∨ q) : p ∨ (q ∨ r) :=
  Or.elim h
    (fun hp : p =>
      Or.intro_left (q ∨ r) hp)
    (fun hq : q =>
      Or.intro_right p (Or.intro_left r hq))

-- SUPPORTING THM FOR ASSOC_OR
lemma assoc_or_right {p q r : Prop} (h: (p ∨ q) ∨ r) : p ∨ (q ∨ r) :=
  Or.elim h
    (fun h =>
      assoc_or_right_sup h)
    (fun hr : r =>
      Or.intro_right p (Or.intro_right q hr))

-- SUPPORTING THM FOR ASSOC_OR_LEFT
lemma assoc_or_left_sup {p q r : Prop} (h : q ∨ r) : (p ∨ q) ∨ r :=
  Or.elim h
    (fun hq : q =>
      Or.intro_left r (Or.intro_right p hq))
    (fun hr : r =>
      Or.intro_right (p ∨ q) hr)

-- SUPPORTING THM FOR ASSOC_OR
lemma assoc_or_left {p q r : Prop} (h: p ∨ (q ∨ r)) : (p ∨ q) ∨ r :=
  Or.elim h
    (fun hp : p =>
      Or.intro_left r (Or.intro_left q hp))
    (fun hqr : q ∨ r =>
      assoc_or_left_sup hqr)

theorem assoc_or_iff {p q r : Prop} : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hl : (p ∨ q) ∨ r =>
      assoc_or_right hl)
    (fun hr : p ∨ (q ∨ r) =>
      assoc_or_left hr)


-- SUPPORT LEMMA FOR ASSOC_AND_IFF →
lemma assoc_and_left {p q r : Prop} : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
  And.elim
    (fun hl hr =>
      And.intro (And.left hl) (And.intro (And.right hl) hr))


-- SUPPORT LEMMA FOR ASSOC_AND_IFF ←
lemma assoc_and_right {p q r : Prop} : p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
  And.elim
    (fun hl hr =>
      And.intro (And.intro hl (And.left hr)) (And.right hr))

theorem assoc_and_iff {p q r : Prop} : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h1 =>
      assoc_and_left h1)
    (fun h2 =>
      assoc_and_right h2
    )

theorem test_terms (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  And.intro hp (And.intro hq hp)

theorem test_tactics (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro hq hp
  case left =>
    apply hp
