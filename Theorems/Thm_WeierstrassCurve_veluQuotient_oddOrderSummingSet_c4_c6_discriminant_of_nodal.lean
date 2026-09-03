import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal
open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0)
    {n : ℕ} (hn : Odd n)
    (Q : W.toAffine.Point) (hQord : addOrderOf Q = n) :
    (W.veluQuotient (W.oddOrderSummingSet Q (n / 2))).c₄ = (n : F) ^ 4 * W.c₄ ∧
    (W.veluQuotient (W.oddOrderSummingSet Q (n / 2))).c₆ = (n : F) ^ 6 * W.c₆ ∧
    (W.veluQuotient (W.oddOrderSummingSet Q (n / 2))).Δ = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.solution
