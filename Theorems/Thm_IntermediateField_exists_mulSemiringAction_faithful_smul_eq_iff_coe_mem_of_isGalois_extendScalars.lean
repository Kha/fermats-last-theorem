import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_mulSemiringAction_faithful_smul_eq_iff_coe_mem_of_isGalois_extendScalars

set_option autoImplicit false

universe u v

theorem IntermediateField.exists_mulSemiringAction_faithful_smul_eq_iff_coe_mem_of_isGalois_extendScalars
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (F E : IntermediateField K L) (hle : F ≤ E)
    [FiniteDimensional ↥F ↥(IntermediateField.extendScalars hle)]
    [IsGalois ↥F ↥(IntermediateField.extendScalars hle)] :
    ∃ (G : Type v) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥E),
      FaithfulSMul G ↥E ∧
      (∀ (g : G) (x : ↥E), (x : L) ∈ F → g • x = x) ∧
      (∀ x : ↥E, (∀ g : G, g • x = x) → (x : L) ∈ F) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_mulSemiringAction_faithful_smul_eq_iff_coe_mem_of_isGalois_extendScalars.solution
