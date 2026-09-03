import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_isDomain_tensorProduct_of_le_laurentSeries
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

set_option autoImplicit false

open scoped TensorProduct

theorem IntermediateField.isDomain_tensorProduct_of_le_laurentSeries
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k]
    (R : IntermediateField κ (LaurentSeries κ)) :
    IsDomain (↥R ⊗[κ] k) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_isDomain_tensorProduct_of_le_laurentSeries.solution
