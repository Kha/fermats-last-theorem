import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isUnipotentOnInertiaAt_of_isUnramifiedAt

set_option autoImplicit false
theorem GaloisRepAdic.isUnipotentOnInertiaAt_of_isUnramifiedAt {A : Type} [CommRing A] [IsLocalRing A]
    (ρ : GaloisRepAdic A) {q : ℕ} (h : ρ.IsUnramifiedAt q) : ρ.IsUnipotentOnInertiaAt q := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isUnipotentOnInertiaAt_of_isUnramifiedAt.solution
