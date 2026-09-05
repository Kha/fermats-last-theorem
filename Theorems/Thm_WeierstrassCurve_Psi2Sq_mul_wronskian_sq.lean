module

public import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq

@[expose] public section

open Polynomial WeierstrassCurve
theorem WeierstrassCurve.Psi2Sq_mul_wronskian_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) : W.Ψ₂Sq * (derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)) ^ 2 = C ((n : R) ^ 2) * (W.ΨSq n * (C 4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n + C (2 * W.b₄) * W.Φ n * W.ΨSq n ^ 2 + C W.b₆ * W.ΨSq n ^ 3)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.solution
