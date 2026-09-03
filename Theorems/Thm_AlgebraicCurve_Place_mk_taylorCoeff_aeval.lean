import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_mk_taylorCoeff_aeval

set_option autoImplicit false

p2m_open "AlgebraicCurve AlgebraicCurve.Place~taylorCoeff_algebraMap~taylorCoeff_add~taylorCoeff_mul~mk_taylorCoeff_evalEval"

theorem AlgebraicCurve.Place.mk_taylorCoeff_aeval {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {σ : Type*} (f : σ → F) (hf : ∀ s, f s ∈ v.toValuationSubring) (H : MvPolynomial σ K) :
    (PowerSeries.mk fun n => taylorCoeff v t n (MvPolynomial.aeval f H))
      = MvPolynomial.aeval (fun s => PowerSeries.mk fun n => taylorCoeff v t n (f s)) H := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_mk_taylorCoeff_aeval.solution
