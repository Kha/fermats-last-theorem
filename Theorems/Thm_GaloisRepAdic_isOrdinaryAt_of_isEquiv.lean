import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isOrdinaryAt_of_isEquiv

theorem GaloisRepAdic.isOrdinaryAt_of_isEquiv
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.IsOrdinaryAt p) : ρ₂.IsOrdinaryAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isOrdinaryAt_of_isEquiv.solution
