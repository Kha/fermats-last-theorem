import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import P2M.Util
import P2M.Sol.S_IsLocalRing_quotient_of_ne_top

theorem IsLocalRing.quotient_of_ne_top
    {A : Type} [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : I ≠ ⊤) :
    IsLocalRing (A ⧸ I) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_quotient_of_ne_top.solution
