import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_x1FunctionFieldBar_coe_eq_coeffMap_of_algEquiv_laurentBaseChange
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one

set_option autoImplicit false

theorem ModularCurve.exists_algEquiv_x1FunctionFieldBar_coe_eq_coeffMap_of_algEquiv_laurentBaseChange
    (N : ℕ) [NeZero N]
    (L : Type) [Field L] [CharZero L] [Algebra L (AlgebraicClosure ℚ)]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (σ : ↥K ≃ₐ[L] ↥K) :
    ∃ σbar : ↥(ModularCurve.x1FunctionFieldBar N) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar N),
      ∀ (f : ↥(ModularCurve.x1FunctionFieldBar N)) (b : ↥K),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
        ((σbar f : ↥(ModularCurve.x1FunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((σ b : ↥K) : LaurentSeries L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_x1FunctionFieldBar_coe_eq_coeffMap_of_algEquiv_laurentBaseChange.solution
