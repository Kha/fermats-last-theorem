import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard

set_option autoImplicit false

universe u v

theorem MvPolynomial.isStandardSmoothOfRelativeDimension_natCard
    (S : Type u) [CommRing S] (ι : Type v) [Finite ι] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) S (MvPolynomial ι S) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard.solution
