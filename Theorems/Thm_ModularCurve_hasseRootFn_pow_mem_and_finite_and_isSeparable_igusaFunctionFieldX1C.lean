import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import P2M.Util
import P2M.Sol.S_ModularCurve_hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularCurve.jqNModC_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (κ : Type) [Field κ] [CharP κ p] (w : ModularCurve.IntegralWeightOneForm κ M) :
    letI : Algebra ↥(ModularCurve.x1FunctionFieldC κ M) ↥(ModularCurve.igusaFunctionFieldX1C κ M w) :=
      (IntermediateField.inclusion (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C κ M w)).toRingHom.toAlgebra
    w.hasseRootFn ^ (p - 1) ∈ ModularCurve.x1FunctionFieldC κ M ∧
    Module.Finite ↥(ModularCurve.x1FunctionFieldC κ M) ↥(ModularCurve.igusaFunctionFieldX1C κ M w) ∧
    Algebra.IsSeparable ↥(ModularCurve.x1FunctionFieldC κ M) ↥(ModularCurve.igusaFunctionFieldX1C κ M w) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C.solution
