import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_isSplittingField_igusaFunctionFieldX1C_X_pow_sub_C

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open ModularCurve CongruenceSubgroup AlgebraicCurve Polynomial
open scoped MatrixGroups

theorem ModularCurve.isSplittingField_igusaFunctionFieldX1C_X_pow_sub_C
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
    (w : ModularCurve.IntegralWeightOneForm Ω M)
    (b : ↥(ModularCurve.x1FunctionFieldC Ω M)) (hb : (b : LaurentSeries Ω) = w.hasseRootFn ^ (p - 1)) :
    letI : Algebra ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w) :=
      (IntermediateField.inclusion (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C Ω M w)).toRingHom.toAlgebra
    IsSplittingField ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w)
      (X ^ (p - 1) - C b) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isSplittingField_igusaFunctionFieldX1C_X_pow_sub_C.solution
