import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_taylorCoeff_mul

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.taylorCoeff_mul
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) (r : ℕ) :
    taylorCoeff v t r (f * g)
      = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r, taylorCoeff v t x.1 f * taylorCoeff v t x.2 g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_taylorCoeff_mul.solution
