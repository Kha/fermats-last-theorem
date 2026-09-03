import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization
import P2M.Util
import P2M.Sol.S_TateCurve_tateTorsionEquiv_add

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve in
theorem TateCurve.tateTorsionEquiv_add
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [DecidableEq K]
    {q ζ t : K} (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    (a b : Fin p × Fin p) :
    ((TateCurve.tateTorsionEquiv q ζ t hq0 hq1 Fact.out hp5 hζ ht (a + b) :
        (TateCurve.curve q).n_torsionGen p) : (TateCurve.curve q).toAffine.Point)
      = ((TateCurve.tateTorsionEquiv q ζ t hq0 hq1 Fact.out hp5 hζ ht a :
        (TateCurve.curve q).n_torsionGen p) : (TateCurve.curve q).toAffine.Point)
      + ((TateCurve.tateTorsionEquiv q ζ t hq0 hq1 Fact.out hp5 hζ ht b :
        (TateCurve.curve q).n_torsionGen p) : (TateCurve.curve q).toAffine.Point) := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_tateTorsionEquiv_add.solution
