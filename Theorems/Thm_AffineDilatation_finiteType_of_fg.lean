import Mathlib
import Definitions.Def_RingTheory_AffineDilatation
import P2M.Util
import P2M.Sol.S_AffineDilatation_finiteType_of_fg

set_option autoImplicit false

universe u v

theorem AffineDilatation.finiteType_of_fg
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (I : Ideal A) (a : A) (hI : I.FG) :
    Algebra.FiniteType R (AffineDilatation.Ring I a) := by p2m_exact_reverting @_root_.P2MW.S_AffineDilatation_finiteType_of_fg.solution
