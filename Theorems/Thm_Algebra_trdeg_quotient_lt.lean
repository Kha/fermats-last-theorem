import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_trdeg_quotient_lt

universe u v

theorem Algebra.trdeg_quotient_lt {K : Type u} {R : Type v} [Field K] [CommRing R] [IsDomain R]
    [Algebra K R] [Algebra.FiniteType K R] (I : Ideal R) (hI : I ≠ ⊥) (hI' : I ≠ ⊤) :
    Algebra.trdeg K (R ⧸ I) < Algebra.trdeg K R := by p2m_exact_reverting @_root_.P2MW.S_Algebra_trdeg_quotient_lt.solution
