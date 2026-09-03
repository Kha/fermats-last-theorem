import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_level_ofChar_cycloChar_comp

set_option autoImplicit false
open CategoryTheory groupCohomology ExtCitation
theorem groupCohomology.exists_level_ofChar_cycloChar_comp
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (m : ofChar (k := ZMod p) ((cycloChar p).comp r)) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → (ofChar (k := ZMod p) ((cycloChar p).comp r)).ρ s m = m := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_level_ofChar_cycloChar_comp.solution
