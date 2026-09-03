import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization
import P2M.Util
import P2M.Sol.S_TateCurve_tateTorsionPoint_snd_eq_nsmul

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve in
theorem TateCurve.tateTorsionPoint_snd_eq_nsmul
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [DecidableEq K]
    {q ζ t : K} (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    {j : ℕ} (hj : j < p) :
    TateCurve.tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 j
      = j • TateCurve.tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 1 := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_tateTorsionPoint_snd_eq_nsmul.solution
