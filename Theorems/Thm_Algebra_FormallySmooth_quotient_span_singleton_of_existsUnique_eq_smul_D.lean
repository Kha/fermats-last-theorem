import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_quotient_span_singleton_of_existsUnique_eq_smul_D

set_option autoImplicit false

theorem Algebra.FormallySmooth.quotient_span_singleton_of_existsUnique_eq_smul_D
    {A : Type} [CommRing A] {S : Type} [CommRing S] [Algebra A S] [Algebra.FormallySmooth A S]
    (t : S) (hdt : ∀ ω : Ω[S⁄A], ∃! s : S, ω = s • KaehlerDifferential.D A S t) :
    Algebra.FormallySmooth A (S ⧸ Ideal.span ({t} : Set S)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_quotient_span_singleton_of_existsUnique_eq_smul_D.solution
