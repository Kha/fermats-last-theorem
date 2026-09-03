import Definitions.Def_GaloisRep_StrictOrdinary
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isStrictOrdinaryAt_of_isEquiv

theorem GaloisRepAdic.isStrictOrdinaryAt_of_isEquiv
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.IsStrictOrdinaryAt p) : ρ₂.IsStrictOrdinaryAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_isEquiv.solution
