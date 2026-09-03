import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_nonempty_algEquiv_of_isLocalRing_of_finite_residueField_of_card_eq

set_option autoImplicit false

open IsLocalRing

theorem Algebra.Etale.nonempty_algEquiv_of_isLocalRing_of_finite_residueField_of_card_eq
    (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [IsAdicComplete (maximalIdeal R₀) R₀]
    (S₁ : Type) [CommRing S₁] [IsLocalRing S₁] [Algebra R₀ S₁] [IsLocalHom (algebraMap R₀ S₁)]
    [Module.Finite R₀ S₁] [Algebra.Etale R₀ S₁]
    (S₂ : Type) [CommRing S₂] [IsLocalRing S₂] [Algebra R₀ S₂] [IsLocalHom (algebraMap R₀ S₂)]
    [Module.Finite R₀ S₂] [Algebra.Etale R₀ S₂]
    [Finite (ResidueField S₁)] [Finite (ResidueField S₂)]
    (h : Nat.card (ResidueField S₁) = Nat.card (ResidueField S₂)) :
    Nonempty (S₁ ≃ₐ[R₀] S₂) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_nonempty_algEquiv_of_isLocalRing_of_finite_residueField_of_card_eq.solution
