import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_int_ne_zero_isIntegral_adjoin_int_of_isIntegral_adjoin_rat

theorem ModularCurve.exists_int_ne_zero_isIntegral_adjoin_int_of_isIntegral_adjoin_rat (t x : LaurentSeries ℚ) (hx : IsIntegral (Algebra.adjoin ℚ ({t} : Set (LaurentSeries ℚ))) x) :
    ∃ d : ℤ, d ≠ 0 ∧
      IsIntegral (Algebra.adjoin ℤ ({t} : Set (LaurentSeries ℚ)))
        (algebraMap ℚ (LaurentSeries ℚ) (d : ℚ) * x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_int_ne_zero_isIntegral_adjoin_int_of_isIntegral_adjoin_rat.solution
