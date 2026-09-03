import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_of_sq_eq_neg_one

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open NumberField
open scoped NumberField.InfPlaceDecomp

theorem NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_of_sq_eq_neg_one
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (i : E) (hi : i ^ 2 = -1)
    (v : InfinitePlace K) (g : K ≃ₐ[E] K) (hg : g ∈ NumberField.InfPlaceDecomp.decomp E K v) : g = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_of_sq_eq_neg_one.solution
