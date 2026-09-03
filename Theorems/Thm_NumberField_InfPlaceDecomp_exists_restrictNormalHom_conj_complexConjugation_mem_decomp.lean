import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_NumberField_InfPlaceDecomp_exists_restrictNormalHom_conj_complexConjugation_mem_decomp
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem NumberField.InfPlaceDecomp.exists_restrictNormalHom_conj_complexConjugation_mem_decomp
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
    (w : InfinitePlace ↥F) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * complexConjugation * σ) ∈ NumberField.InfPlaceDecomp.decomp ℚ ↥F w ∧
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * complexConjugation * σ) ≠ 1 ∧
      (∀ d : ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F w),
        (d : ↥F ≃ₐ[ℚ] ↥F) = 1 ∨ (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * complexConjugation * σ)) ∧
      σ⁻¹ * complexConjugation * σ ∉ F.fixingSubgroup := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfPlaceDecomp_exists_restrictNormalHom_conj_complexConjugation_mem_decomp.solution
