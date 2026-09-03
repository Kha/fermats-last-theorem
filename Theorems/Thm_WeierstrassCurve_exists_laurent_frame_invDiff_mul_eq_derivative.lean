import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_laurent_frame_invDiff_mul_eq_derivative

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.exists_laurent_frame_invDiff_mul_eq_derivative
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (G : FormalGroup R)
    (hG : G.toPowerSeries = W.formalGroupLawFixed) :
    ∃ x y : LaurentSeries R,
      y ^ 2 + HahnSeries.C W.a₁ * x * y + HahnSeries.C W.a₃ * y
          = x ^ 3 + HahnSeries.C W.a₂ * x ^ 2 + HahnSeries.C W.a₄ * x + HahnSeries.C W.a₆ ∧
      x.coeff (-2) = 1 ∧ (∀ n < -2, x.coeff n = 0) ∧ y.coeff (-3) = -1 ∧ (∀ n < -3, y.coeff n = 0) ∧
      HahnSeries.ofPowerSeries ℤ R G.invDiff * (2 * y + HahnSeries.C W.a₁ * x + HahnSeries.C W.a₃)
        = LaurentSeries.derivative R x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_laurent_frame_invDiff_mul_eq_derivative.solution
