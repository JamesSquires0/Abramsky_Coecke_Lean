-- These are proofs from Worksheet 2 of MATH 4010
import Mathlib.Tactic
namespace Group_Basics

-- We define a group as a class structure (class structures are essentially)
class Group (G : Type u) where
  -- The binary operation mul: closure is built in, as it maps back to G
  mul : G → G → G
  -- Associativity of our multiplication
  assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  -- Identity Element
  e : G
  -- Left and right multiplication of identity respectively
  el_mul : ∀ a : G, mul e a = a
  er_mul : ∀ a : G, mul a e = a
  -- Existence of inverse for all elements
  inv : G → G
  inv_l : ∀ a : G, mul (inv a) a = e
  inv_r : ∀ a : G, mul a (inv a) = e

-- To make our life easier, we add these basic operations to the simp tactic
attribute [simp] Group.assoc Group.el_mul Group.er_mul Group.inv_l Group.inv_r

-- Let's make group multiplication feel more natural
infixl:70 " * " => Group.mul

variable {G : Type u} [Group G]

-- Uniqueness of Identity
lemma unique_e (e' : G) : (∀ a : G, Group.mul e' a = a) → e' = Group.e :=
  fun h_e =>
    -- Need e' = e
    Eq.symm
    -- Need e = e' * e = e'
    (Eq.trans
    -- e = e' * e
    (Eq.symm (h_e Group.e))
    -- e' * e = e'
    (Group.er_mul e'))

-- Uniqueness of inverse
-- We want a inv(a) = e = a inv(a)' → inv(a) = inv(a)'
lemma unique_e_tact (e' : G) : (∀ a : G, Group.mul e' a = a) → e' = Group.e := by
  intro h_e
  apply Eq.symm
  apply Eq.trans
  apply Eq.symm (h_e Group.e)
  exact (Group.er_mul e')

-- Support lemmas for future proofs
lemma mul_right_cancel {a b c : G} : a * b = c * b → a = c := by
  intro h
  have h_simp := congrArg (fun x => Group.mul x (Group.inv b)) h
  simp at h_simp
  exact h_simp

lemma mul_right_add {a c : G} (b : G) (h_eq : a = c) : a * b = c * b := by
  have h_mul := congrArg (fun x => x * b) h_eq
  simp at h_mul
  exact h_mul

--attribute [simp] mul_right_cancel mul_right_add

-- We want to show the uniqueness of left inverse
lemma unique_l_inv_tact (i a : G) : (i * a = Group.e) → i = Group.inv a := by
-- We have i * a = e
-- Now we also want inv(a) * a = e. Then we want inv(a) * a = i * a.
-- Then we want to take the inv(a) on the left of both sides.
intro h_inv
have h_eq : (Group.inv a) * a = i * a := by
 rw [h_inv, Group.inv_l]
have h_simp := congrArg (fun x => x * (Group.inv a)) h_eq
simp at h_simp
apply Eq.symm
apply h_simp

-- The inverse of the inverse of a is just a
lemma inv_inv_a (a : G) : Group.inv (Group.inv a) = a := by
  have h_invinv : Group.inv (Group.inv a) * (Group.inv a) = Group.e := by
   apply Group.inv_l (Group.inv a)
  have h_inv_mul : (Group.inv (Group.inv a) * (Group.inv a)) * a = Group.e * a := by
    apply mul_right_add (a) h_invinv
  rw [Group.assoc] at h_inv_mul
  rw [Group.inv_l] at h_inv_mul
  rw [Group.er_mul] at h_inv_mul
  rw [Group.el_mul a] at h_inv_mul
  exact h_inv_mul

-- Defining homomorphisms
structure GroupHom (G H : Type u) [Group G] [Group H] where
  -- φ(xy) = φ(x)φ(y)
  map : G → H
  map_mul : ∀ x y : G, map (x * y) = (map x) * (map y)


end Group_Basics
