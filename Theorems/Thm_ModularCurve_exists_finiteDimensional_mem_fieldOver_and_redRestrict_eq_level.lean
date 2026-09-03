import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq_level
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

theorem ModularCurve.exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq_level
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {k : Type*} [Field k] (red : A →+* k) (a : k) (ha : a ∈ Set.range red) (M : ℕ) [NeZero M]
    (f : ↥(modularFunctionFieldBar M)) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K),
      ((f : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver M K) ∧
        (∃ x : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K x = a) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq_level.solution
