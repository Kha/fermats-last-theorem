import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization
import P2M.Util
import P2M.Sol.S_TateCurve_tateTorsionPoint_map

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve in
theorem TateCurve.tateTorsionPoint_map
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [DecidableEq K]
    {q ζ t : K} (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    (σ : K →+* K) (hσ : Isometry ⇑σ) (hσq : σ q = q)
    {e c : ℕ} (hσζ : σ ζ = ζ ^ e) (hσt : σ t = ζ ^ c * t)
    {i j : ℕ} (hi : i < p) (hj : j < p) (hij : ¬(i = 0 ∧ j = 0))
    (hns' : (TateCurve.curve q).toAffine.Nonsingular
      (σ (TateCurve.pointX q (ζ ^ i * t ^ j))) (σ (TateCurve.pointY q (ζ ^ i * t ^ j)))) :
    (WeierstrassCurve.Affine.Point.some
        (σ (TateCurve.pointX q (ζ ^ i * t ^ j))) (σ (TateCurve.pointY q (ζ ^ i * t ^ j))) hns'
      : (TateCurve.curve q).toAffine.Point)
      = TateCurve.tateTorsionPoint q ζ t hq0 hq1 hp hζ ht ((e * i + c * j) % p) j := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_tateTorsionPoint_map.solution
