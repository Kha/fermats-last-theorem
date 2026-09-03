import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits

set_option autoImplicit false

open CategoryTheory groupCohomology
theorem groupCohomology.exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (L : IntermediateField K Ω) [Normal K L]
    (hL : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ L.fixingSubgroup) :
    ∃ inf : H2 (Rep.ofAlgebraAutOnUnits K L) →ₗ[ℤ] continuousH2 r (Rep.ofAlgebraAutOnUnits K Ω),
      ∀ (f : cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
        (hf' : unitsInflate₂ L f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω)),
        inf (H2π (Rep.ofAlgebraAutOnUnits K L) f) =
          continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) ⟨unitsInflate₂ L f, hf'⟩ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits.solution
