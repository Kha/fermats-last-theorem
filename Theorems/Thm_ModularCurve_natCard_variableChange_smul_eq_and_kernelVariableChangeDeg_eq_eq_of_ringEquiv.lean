import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import P2M.Util
import P2M.Sol.S_ModularCurve_natCard_variableChange_smul_eq_and_kernelVariableChangeDeg_eq_eq_of_ringEquiv

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.natCard_variableChange_smul_eq_and_kernelVariableChangeDeg_eq_eq_of_ringEquiv
    {K K' : Type u} [Field K] [Field K'] (σ : K ≃+* K')
    (W : WeierstrassCurve K) {I : Type u} (d : I → ℕ) (T : I → Polynomial K) :
    Nat.card {C : WeierstrassCurve.VariableChange K //
        C • W = W ∧ ∀ i, ModularCurve.kernelVariableChangeDeg C (d i) (T i) = T i} =
      Nat.card {C' : WeierstrassCurve.VariableChange K' //
        C' • (W.map (σ : K →+* K')) = W.map (σ : K →+* K') ∧
          ∀ i, ModularCurve.kernelVariableChangeDeg C' (d i) ((T i).map (σ : K →+* K')) = (T i).map (σ : K →+* K')} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_natCard_variableChange_smul_eq_and_kernelVariableChangeDeg_eq_eq_of_ringEquiv.solution
