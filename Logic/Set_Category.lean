import Mathlib.CategoryTheory.Category.Basic

universe u

instance : CategoryTheory.CategoryStruct (Type u) where
  Hom (X : Type u) (Y : Type u) := X → Y
  id (X : Type u) := fun (x : X) => x
  comp {X Y Z : Type u} (f : X → Y) (g : Y → Z) := fun (x : X) => g (f x)

instance : CategoryTheory.Category (Type u) where
  id_comp {X Y : Type u} (f : X → Y) := by
    apply funext
    intro (x : X)
    rfl

  comp_id {X Y : Type u} (f : X → Y) := by
    apply funext
    intro (x : X)
    rfl

  assoc {W X Y Z : Type u} (f : W → X) (g : X → Y) (h : Y → Z) := by
    apply funext
    intro (w : W)
    rfl
