import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_IsDrinfeldBasisAdic_map_of_isBaseChange

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.IsDrinfeldBasisAdic.map_of_isBaseChange
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) [IsAdicComplete I R] [IsAdicComplete J S]
    (f : R →+* S) (hf : ∀ r ∈ I, f r ∈ J) (F : FormalGroup R) (G : FormalGroup S) (h : F.IsBaseChange f G)
    (q : ℕ) (x₀ x₁ : R) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (hD : F.IsDrinfeldBasisAdic I q x₀ x₁) :
    G.IsDrinfeldBasisAdic J q (f x₀) (f x₁) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_IsDrinfeldBasisAdic_map_of_isBaseChange.solution
