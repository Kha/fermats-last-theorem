import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_flatCondition_of_isEquiv

theorem GaloisRepAdic.flatCondition_of_isEquiv
    {A : Type} [CommRing A] [IsLocalRing A]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.flatCondition 𝒪 p S ρ₁) : GaloisRep.flatCondition 𝒪 p S ρ₂ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_flatCondition_of_isEquiv.solution
