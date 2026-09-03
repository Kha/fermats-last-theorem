import Mathlib
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_unitsInflate2_eq_of_le

set_option autoImplicit false

open CategoryTheory groupCohomology
theorem groupCohomology.exists_unitsInflate2_eq_of_le
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (L L' : IntermediateField K Ω) [Normal K L] [Normal K L'] (hLL' : L ≤ L')
    (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ) (hf : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L)) :
    ∃ f' : (L' ≃ₐ[K] L') × (L' ≃ₐ[K] L') → Additive (L')ˣ,
      f' ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L') ∧ unitsInflate₂ L' f' = unitsInflate₂ L f := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_unitsInflate2_eq_of_le.solution
