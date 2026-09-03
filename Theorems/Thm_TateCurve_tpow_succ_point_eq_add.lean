import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization
import P2M.Util
import P2M.Sol.S_TateCurve_tpow_succ_point_eq_add

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve in
theorem TateCurve.tpow_succ_point_eq_add
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [DecidableEq K]
    {q ζ t : K} (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    {j : ℕ} (hj1 : 1 ≤ j) (hjp : j + 1 < p)
    (h₁ : (TateCurve.curve q).toAffine.Nonsingular
      (TateCurve.pointX q (t ^ (j + 1))) (TateCurve.pointY q (t ^ (j + 1))))
    (h₂ : (TateCurve.curve q).toAffine.Nonsingular (TateCurve.pointX q t) (TateCurve.pointY q t))
    (h₃ : (TateCurve.curve q).toAffine.Nonsingular
      (TateCurve.pointX q (t ^ j)) (TateCurve.pointY q (t ^ j))) :
    (WeierstrassCurve.Affine.Point.some (TateCurve.pointX q (t ^ (j + 1)))
        (TateCurve.pointY q (t ^ (j + 1))) h₁ : (TateCurve.curve q).toAffine.Point)
      = WeierstrassCurve.Affine.Point.some (TateCurve.pointX q t) (TateCurve.pointY q t) h₂
        + WeierstrassCurve.Affine.Point.some (TateCurve.pointX q (t ^ j))
            (TateCurve.pointY q (t ^ j)) h₃ := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_tpow_succ_point_eq_add.solution
