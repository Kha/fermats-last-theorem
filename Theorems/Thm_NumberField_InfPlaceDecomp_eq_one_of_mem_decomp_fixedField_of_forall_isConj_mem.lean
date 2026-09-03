import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_of_forall_isConj_mem
set_option autoImplicit false
set_option maxHeartbeats 200000
open NumberField

theorem NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_fixedField_of_forall_isConj_mem
    (E C : Type) [Field E] [NumberField E] [Field C] [NumberField C] [Algebra E C] [IsGalois E C]
    (M : Subgroup (C ≃ₐ[E] C))
    (hM : ∀ (φ : C →+* ℂ) (σ : C ≃ₐ[E] C), NumberField.ComplexEmbedding.IsConj φ σ → σ ∈ M)
    [IsGalois E (IntermediateField.fixedField M)] :
    ∀ (w : InfinitePlace (IntermediateField.fixedField M)) (g : (IntermediateField.fixedField M) ≃ₐ[E] (IntermediateField.fixedField M)),
      g ∈ NumberField.InfPlaceDecomp.decomp E (IntermediateField.fixedField M) w → g = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_of_forall_isConj_mem.solution
