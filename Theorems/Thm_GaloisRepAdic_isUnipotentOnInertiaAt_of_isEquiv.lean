import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isUnipotentOnInertiaAt_of_isEquiv

theorem GaloisRepAdic.isUnipotentOnInertiaAt_of_isEquiv
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {q : ℕ}
    (h : ρ₁.IsUnipotentOnInertiaAt q) : ρ₂.IsUnipotentOnInertiaAt q := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isUnipotentOnInertiaAt_of_isEquiv.solution
