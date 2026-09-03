import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import P2M.Util
import P2M.Sol.S_groupCohomology_unitsInflate2_mem_levelCocycles2

set_option autoImplicit false

open CategoryTheory groupCohomology
theorem groupCohomology.unitsInflate2_mem_levelCocycles2
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (L : IntermediateField K Ω) [Normal K L]
    (hL : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ L.fixingSubgroup)
    {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ}
    (hf : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L)) :
    unitsInflate₂ L f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_unitsInflate2_mem_levelCocycles2.solution
