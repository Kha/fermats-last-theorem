import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing

set_option autoImplicit false

theorem AlgHom.exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing
    (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [IsAlgClosed K]
    (H : Type*) [CommRing H] [Algebra A H] [Module.Finite A H] [Module.Flat A H]
    (ψ : H →ₐ[A] IsLocalRing.ResidueField A) :
    ∃ φ : H →ₐ[A] A, ∀ h : H, IsLocalRing.residue A (φ h) = ψ h := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.solution
