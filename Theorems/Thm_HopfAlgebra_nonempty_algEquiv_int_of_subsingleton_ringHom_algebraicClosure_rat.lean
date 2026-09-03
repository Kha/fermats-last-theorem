import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_nonempty_algEquiv_int_of_subsingleton_ringHom_algebraicClosure_rat

theorem HopfAlgebra.nonempty_algEquiv_int_of_subsingleton_ringHom_algebraicClosure_rat
    (R : Type) [CommRing R] [HopfAlgebra ℤ R] [Module.Flat ℤ R] [Algebra.FiniteType ℤ R]
    (huniq : ∀ f g : R →+* AlgebraicClosure ℚ, f = g) :
    Nonempty (R ≃ₐ[ℤ] ℤ) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_nonempty_algEquiv_int_of_subsingleton_ringHom_algebraicClosure_rat.solution
