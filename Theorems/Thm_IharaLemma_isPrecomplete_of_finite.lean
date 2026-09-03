import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Finiteness.Defs
import P2M.Util
import P2M.Sol.S_IharaLemma_isPrecomplete_of_finite

set_option autoImplicit false

theorem IharaLemma.isPrecomplete_of_finite {R : Type*} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_isPrecomplete_of_finite.solution
