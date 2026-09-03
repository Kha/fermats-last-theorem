import Mathlib
import P2M.Util
import P2M.Sol.S_FixedPart_isReduced_of_linearIndependent_of_trace

set_option autoImplicit false

open Submodule

theorem FixedPart.isReduced_of_linearIndependent_of_trace
    (R : Type) [CommRing R] [Module.Free ℤ R] [Module.Finite ℤ R]
    (hsep : ∀ r : R, r ≠ 0 → ∃ s : R, Algebra.trace ℤ R (r * s) ≠ 0)
    (q : ℕ) [Fact q.Prime] (T : Type) [CommRing T] [Algebra ℚ_[q] T] (f : R →+* T)
    (hspan : Algebra.adjoin ℚ_[q] (Set.range f) = ⊤)
    (hli : LinearIndependent ℚ_[q] fun i => f (Module.Free.chooseBasis ℤ R i)) :
    IsReduced T ∧ IsArtinianRing T := by p2m_exact_reverting @_root_.P2MW.S_FixedPart_isReduced_of_linearIndependent_of_trace.solution
