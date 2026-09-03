import Mathlib
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_LegendreJ
import Definitions.Def_ModularCurve_JWidth
import P2M.Util
import P2M.Sol.S_ModularCurve_sum_inv_jWidth_of_deuringPolynomial

open Polynomial ModularCurve
theorem ModularCurve.sum_inv_jWidth_of_deuringPolynomial (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    ∑ j ∈ ((deuringPolynomial q).map (Int.castRingHom K)).roots.toFinset.image legendreJ,
      ((jWidth j : ℚ))⁻¹ = ((q : ℚ) - 1) / 12 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sum_inv_jWidth_of_deuringPolynomial.solution
