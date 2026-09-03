import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_LegendreJ
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_hasseInvariant_legendreCurve

open Polynomial WeierstrassCurve
theorem WeierstrassCurve.hasseInvariant_legendreCurve {R : Type*} [CommRing R] {q : ℕ} (hq : Odd q) (t : R) :
    (legendreCurve t).hasseInvariant q
      = (-4) ^ ((q - 1) / 2) * ((Polynomial.deuringPolynomial q).map (Int.castRingHom R)).eval t := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_hasseInvariant_legendreCurve.solution
