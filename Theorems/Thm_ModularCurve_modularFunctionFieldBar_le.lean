import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_modularFunctionFieldBar_le

theorem ModularCurve.modularFunctionFieldBar_le (N : ℕ) [NeZero N] {M : ℕ} [NeZero M] (h : N ∣ M) : ModularCurve.modularFunctionFieldBar N ≤ ModularCurve.modularFunctionFieldBar M := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularFunctionFieldBar_le.solution
