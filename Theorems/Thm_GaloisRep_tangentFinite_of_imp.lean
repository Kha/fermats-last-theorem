import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_tangentFinite_of_imp

open IsLocalRing
theorem GaloisRep.tangentFinite_of_imp (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A), 𝒟 ρ → 𝒟' ρ)
    (hfin : TangentFinite 𝒪 ρbar 𝒟') : TangentFinite 𝒪 ρbar 𝒟 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_tangentFinite_of_imp.solution
