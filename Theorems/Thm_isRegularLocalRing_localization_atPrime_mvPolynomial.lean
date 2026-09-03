import Mathlib
import P2M.Util
import P2M.Sol.S_isRegularLocalRing_localization_atPrime_mvPolynomial
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

theorem isRegularLocalRing_localization_atPrime_mvPolynomial
    (k : Type*) [Field k] (n : ℕ) (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by p2m_exact_reverting @_root_.P2MW.S_isRegularLocalRing_localization_atPrime_mvPolynomial.solution
