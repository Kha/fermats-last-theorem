import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_veluX_eq_div_and_veluY_eq_div_of_addOrderOf_eq

theorem WeierstrassCurve.exists_veluX_eq_div_and_veluY_eq_div_of_addOrderOf_eq
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    ∃ (P S N₀ N₁ R : Polynomial F) (B : Finset F), P.Monic ∧ P.natDegree = S.natDegree + 1 ∧
      IsCoprime P S ∧
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        (x ∈ B ↔ (.some x y h : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q)) ∧
      ∀ x : F, x ∉ B → S.eval x ≠ 0 ∧ R.eval x ≠ 0 ∧
        W.veluX (W.oddOrderSummingSet Q n) x = P.eval x / S.eval x ∧
        ∀ y : F, W.veluY (W.oddOrderSummingSet Q n) x y
          = (N₀.eval x + N₁.eval x * y) / R.eval x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_veluX_eq_div_and_veluY_eq_div_of_addOrderOf_eq.solution
