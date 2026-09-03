import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularForm_exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

set_option autoImplicit false

open CongruenceSubgroup ModularForm
open scoped ModularForm MatrixGroups

theorem ModularForm.exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∃ (k : ℤ) (G : ModularForm (Gamma1 p) (k + 1)) (H : ModularForm (Gamma1 p) k)
      (pG pH : PowerSeries ℤ),
      ModularCurve.IsIntegralQExp G pG ∧ ModularCurve.IsIntegralQExp H pH ∧
      pH.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
      pG.map (Int.castRingHom (ZMod p)) = pH.map (Int.castRingHom (ZMod p)) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq.solution
