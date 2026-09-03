import Mathlib
import Definitions.Def_ModularCurve_X1Diamond
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isDiamondAut

theorem ModularCurve.exists_isDiamondAut (M : ℕ) [NeZero M] {d : ℕ} (hd : Nat.Coprime d M) :
    ∃ σ : ModularCurve.x1FunctionField M ≃ₐ[ℚ] ModularCurve.x1FunctionField M,
      ModularCurve.IsDiamondAut M d σ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isDiamondAut.solution
