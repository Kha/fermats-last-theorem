import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_levelAutBar_mul

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.levelAutBar_mul (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M')
    (ζ : ModularCurve.FullLevel.Idx q) (α β : SL(2, ℤ)) (hα : α ∈ CongruenceSubgroup.Gamma0 M')
    (hβ : β ∈ CongruenceSubgroup.Gamma0 M') :
    ModularCurve.FullLevel.levelAutBar q M' ζ (α * β) =
      (ModularCurve.FullLevel.levelAutBar q M' ζ α).trans (ModularCurve.FullLevel.levelAutBar q M' ζ β) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_levelAutBar_mul.solution
