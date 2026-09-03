import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_exists_algEquiv_residue_eq_of_isLocalRing_of_isAdicComplete

set_option autoImplicit false

universe u

p2m_open "IsLocalRing~isAdicComplete_of_module_finite"

theorem Algebra.Etale.exists_algEquiv_residue_eq_of_isLocalRing_of_isAdicComplete
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra R A] [Algebra R B] [Module.Finite R A] [Module.Finite R B]
    [Algebra.Etale R A] [Algebra.Etale R B]
    [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap R B)]
    (e₀ : ResidueField A ≃ₐ[ResidueField R] ResidueField B) :
    ∃ e : A ≃ₐ[R] B, ∀ a : A, residue B (e a) = e₀ (residue A a) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_exists_algEquiv_residue_eq_of_isLocalRing_of_isAdicComplete.solution
