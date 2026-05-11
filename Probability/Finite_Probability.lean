import Mathlib

namespace FiniteSampleSpace

universe u

-- Constructive definition of finite sample space with a Probability Mass Function
-- Could also use Kolmogorov's axioms (only need 2 with finite), but these are ~less constructive
structure SampleSpace (Ω : Type u) [Fintype Ω] where
  -- A probability is a mapping from the samplespace to the reals
  P : Ω → ℝ
  -- Constructive axiom 1: the image of this mapping must be non-negative
  non_neg : ∀ ω, 0 ≤ P ω
  -- Constructive axiom 2 (unit measure): the sum of P over our Ω must equal one
  normalized : (Finset.univ.sum P) = 1

-- The distribution defined with the condition: ∀ χ ∈ Ω, P(x = χ) = 1/k
-- Note: I'm pretty sure this could be made constructive with some modification
noncomputable def uniform_PMF (Ω : Type u) [Fintype Ω] [Nonempty Ω] : SampleSpace Ω where
  P := fun _ => 1 / (Fintype.card Ω : ℝ)
  non_neg := by
    intro ω
    positivity
  normalized := by
    simp

  end FiniteSampleSpace
