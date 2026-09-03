import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_IntermediateField_injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem IntermediateField.injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries
    (κ : Type u) [Field κ] (k : Type v) [Field k] [Algebra κ k]
    (R : IntermediateField κ (LaurentSeries κ))
    (φ : k ⊗[κ] ↥R →ₐ[k] LaurentSeries k)
    (hφ : ∀ r : ↥R, φ (1 ⊗ₜ[κ] r) = ModularCurve.coeffMap (algebraMap κ k) ((r : ↥R) : LaurentSeries κ)) :
    Function.Injective φ := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries.solution
