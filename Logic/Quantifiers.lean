import Mathlib.Tactic

namespace Exercise4dot6
lemma forall_and_r {α : Type} {p q : α → Prop}: (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) :=
  fun h =>
    And.intro
      (fun h1 => (And.left (h h1)))
      (fun h1 => (And.right (h h1)))

lemma forall_and_l {α : Type} {p q : α → Prop} : ((∀ x, p x) ∧ (∀ x, q x)) → (∀ x, p x ∧ q x) :=
  fun h x =>
    And.intro ((And.left h) x) ((And.right h) x)


theorem forall_and_iff {α : Type} {p q : α → Prop} : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (forall_and_r) (forall_and_l)


theorem forall_modus_ponens {α : Type} {p q : α → Prop} : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hpq =>
    fun hp =>
      fun x =>
        hpq x (hp x)

theorem forall_MP_or {α : Type} {p q : α → Prop} : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h =>
    fun x =>
      (Or.elim h)
        (fun hl => Or.intro_left (q x) (hl x))
        (fun hr => Or.intro_right (p x) (hr x))


theorem tautology_forall {r : Prop} {α : Type} {p q : α → Prop} : α → ((∀ x : α, r) ↔ r) :=
  fun alpha => Iff.intro (fun h => h alpha) (fun hr x => hr)

theorem existential_and_comm {α : Type} {p q : α → Prop} : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun h : ∃ x, p x ∧ q x =>
    Exists.elim h (fun w hw =>
      Exists.intro w (And.intro hw.right hw.left))


end Exercise4dot6
