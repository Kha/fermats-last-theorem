import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import P2M.Util
import P2M.Sol.S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_sylow
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_fixedField_sylow
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (P : Sylow p (F ≃ₐ[E] F))
    (hinf2 : p = 2 → ∀ (v : InfinitePlace F) (g : F ≃ₐ[E] F), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)
    (v : InfinitePlace F) (g : (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F)) (hg : g ∈ NumberField.InfPlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v) : g = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_sylow.solution
