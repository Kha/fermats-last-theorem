import Mathlib
import Definitions.Def_Mathlib_RingTheory_KmfloorsFiberPolynomialRegularAscent
import P2M.Util
namespace P2MW.S_isRegularLocalRing_localization_atPrime_mvPolynomial

set_option autoImplicit false

theorem solution (k : Type*) [Field k] (n : ℕ) (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI := kmf2_polyasc_isRegularRing_mvPolynomial_fin k n
  exact IsRegularRing.isRegularLocalRing_localization q
