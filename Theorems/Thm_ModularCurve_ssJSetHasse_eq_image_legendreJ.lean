import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_LegendreJ
import P2M.Util
import P2M.Sol.S_ModularCurve_ssJSetHasse_eq_image_legendreJ

open Polynomial ModularCurve
theorem ModularCurve.ssJSetHasse_eq_image_legendreJ (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (K : Type*) [Field K]
    [IsAlgClosed K] [CharP K q] :
    ssJSetHasse q K
      = legendreJ '' {t | ((Polynomial.deuringPolynomial q).map (Int.castRingHom K)).eval t = 0} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ssJSetHasse_eq_image_legendreJ.solution
