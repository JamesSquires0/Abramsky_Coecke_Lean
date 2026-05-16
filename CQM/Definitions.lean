import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.Tactic.Widget.StringDiagram

open CategoryTheory MonoidalCategory RigidCategory
open ExactPairing

-- Type class resolution for compact closed category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [RigidCategory C]

-- Objects
variable {A B : C}

#check HasLeftDual.leftDual B

-- Snake identity for A
theorem SnakeIdentity (A : C) :
    (rightUnitor A).inv
    ≫ tensorHom (𝟙 A) (coevaluation ᘁA A)
    ≫ (α_ A (ᘁA) A).inv
    ≫ tensorHom (evaluation ᘁA A) (𝟙 A)
    ≫ (leftUnitor A).hom
    = 𝟙 A := by
  with_panel_widgets [Mathlib.Tactic.Widget.StringDiagram]
  aesop_cat

theorem Dual_SnakeIdentity (A : C) :
    (leftUnitor ᘁA).inv
    ≫ tensorHom (coevaluation ᘁA A) (𝟙 (ᘁA))
    ≫ (α_ (ᘁA) A (ᘁA)).hom
    ≫ tensorHom (𝟙 ᘁA) (evaluation ᘁA A)
    ≫ (rightUnitor ᘁA).hom
    = 𝟙 (ᘁ(A) : C) := by
  with_panel_widgets [Mathlib.Tactic.Widget.StringDiagram]
  aesop_cat

-- Names and conames
def name {A B : C} (f : A ⟶ B) : (𝟙_ C) ⟶ (tensorObj (ᘁA : C) B) :=
  (coevaluation ᘁA A) ≫ tensorHom (𝟙 ᘁA) f

def coname {A B : C} {f : A ⟶ B} : (tensorObj A (ᘁB : C)) ⟶ 𝟙_ C :=
  (tensorHom f (𝟙 ᘁB)) ≫ (evaluation (HasLeftDual.leftDual B) B)

-- *-autonomous functor (transpose functor) definition
def transpose {A B : C} (f : A ⟶ B): (ᘁB) ⟶ (ᘁA) :=
  (leftUnitor (ᘁB)).inv ≫ (tensorHom (coevaluation (ᘁA) A) (𝟙 ᘁB))
  ≫ (α_ (ᘁA) A (ᘁB)).hom
  ≫ tensorHom (𝟙 ᘁA) (tensorHom f (𝟙 (ᘁB : C)))
  ≫ tensorHom (𝟙 (ᘁA : C)) (evaluation (HasLeftDual.leftDual B) B)
  ≫ (rightUnitor ᘁA).hom

lemma transpose_compositionality {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
transpose (f ≫ g) = (transpose g) ≫ (transpose f) := by
  with_panel_widgets [Mathlib.Tactic.Widget.StringDiagram]
  sorry
--def transposeFunctorial : Cᵒᵖ ⥤ C where
  --obj A := ᘁ(A.unop)
  --map {A B} f := transpose f.unop
  --map_id A := transpose_id A.unop
  --map_comp f g := transpose_comp f.unop g.unop

-- Natural isomorphism d_A : A → A**
--theorem doubleDualIso {A : C} : A ≅ ᘁᘁA where
  --hom := by
    --with_panel_widgets [Mathlib.Tactic.Widget.StringDiagram]
    --exact (rightUnitor A).inv ≫ (coevaluation (ᘁ(ᘁA)) (ᘁA))
   -- ≫ tensorHom (𝟙 A) (β_ (ᘁ(ᘁA)) (ᘁA)) ≫
