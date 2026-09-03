import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_transcendental_and_finiteDimensional_adjoin_of_valuations

set_option autoImplicit false

open scoped WithZero

theorem AlgebraicCurve.transcendental_and_finiteDimensional_adjoin_of_valuations
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (V : Set (Valuation F ℤᵐ⁰))
    (hK : ∀ v ∈ V, ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 1)
    (hres : ∀ v ∈ V, ∀ f : F, v f = 1 → ∃ c : K, v (f - algebraMap K F c) < 1)
    (hfin : ∀ f : F, f ≠ 0 → {v ∈ V | 1 < v f}.Finite)
    (hconst : ∀ f : F, (∀ v ∈ V, v f ≤ 1) → f ∈ Set.range (algebraMap K F))
    (f : F) (hf : f ∉ Set.range (algebraMap K F)) :
    Transcendental K f ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({f} : Set F)) F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_transcendental_and_finiteDimensional_adjoin_of_valuations.solution
