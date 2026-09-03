import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
namespace P2MW.S_GaloisRepAdic_isUnipotentOnInertiaAt_of_isUnramifiedAt

set_option autoImplicit false

theorem solution {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {q : ℕ}
    (h : ρ.IsUnramifiedAt q) : ρ.IsUnipotentOnInertiaAt q := by
  intro P hP σ hσ
  rw [h P hP σ hσ, LinearMap.charpoly_one, ρ.finrank_eq]
