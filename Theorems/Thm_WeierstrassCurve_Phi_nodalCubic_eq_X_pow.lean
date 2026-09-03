import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Phi_nodalCubic_eq_X_pow

universe u

theorem WeierstrassCurve.Phi_nodalCubic_eq_X_pow (R : Type u) [CommRing R] (n : ℤ) :
    (WeierstrassCurve.mk 1 0 0 0 0 : WeierstrassCurve R).Φ n = Polynomial.X ^ (n.natAbs ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Phi_nodalCubic_eq_X_pow.solution
