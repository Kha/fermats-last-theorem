import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import P2M.Util
import P2M.Sol.S_groupCohomology_mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2

set_option autoImplicit false

open CategoryTheory groupCohomology
theorem groupCohomology.mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (L : IntermediateField K Ω) [FiniteDimensional K L] [Normal K L]
    {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ}
    (hf : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
    (h : unitsInflate₂ L f ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω)) :
    f ∈ coboundaries₂ (Rep.ofAlgebraAutOnUnits K L) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2.solution
