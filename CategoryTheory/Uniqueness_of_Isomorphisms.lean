import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory
universe v u

variable (C : Type u) [CategoryTheory.Category.{v} C]

theorem inv_unique (X Y : C) (f : X ⟶ Y) (g1 g2 : Y ⟶ X)
  (h1_left : f ≫ g1 = CategoryTheory.CategoryStruct.id X)
  (h2_right : g2 ≫ f = CategoryTheory.CategoryStruct.id Y) :
  g1 = g2 := by
  calc
    g1 = 𝟙 Y ≫ g1 := by rw [Category.id_comp]
    _ = (g2 ≫ f) ≫ g1 := by rw [h2_right]
    _ = g2 ≫ (f ≫ g1) := by rw [Category.assoc]
    _ = g2 ≫ 𝟙 X := by rw [h1_left]
    _ = g2 := by rw [Category.comp_id]
