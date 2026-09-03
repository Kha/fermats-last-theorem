import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_exists_ringHom_forall_ghostComponent_eq_iterate_of_frobeniusLift

set_option autoImplicit false

universe u

theorem WittVector.exists_ringHom_forall_ghostComponent_eq_iterate_of_frobeniusLift
    {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ nonZeroDivisors R)
    (σ : R →+* R) (hσ : ∀ a : R, σ a - a ^ p ∈ Ideal.span {(p : R)}) :
    ∃ s : R →+* WittVector p R, ∀ (a : R) (n : ℕ),
      WittVector.ghostComponent n (s a) = (⇑σ)^[n] a := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_ringHom_forall_ghostComponent_eq_iterate_of_frobeniusLift.solution
