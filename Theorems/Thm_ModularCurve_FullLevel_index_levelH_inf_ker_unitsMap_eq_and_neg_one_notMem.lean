import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_index_levelH_inf_ker_unitsMap_eq_and_neg_one_notMem

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.index_levelH_inf_ker_unitsMap_eq_and_neg_one_notMem
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hcop : Nat.Coprime q M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg3 : 3 ≤ ℓg) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) :
    H₁.index = Nat.totient q * (ℓg - 1) ∧ (-1 : (ZMod (q ^ 2 * M'))ˣ) ∉ H₁ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_index_levelH_inf_ker_unitsMap_eq_and_neg_one_notMem.solution
