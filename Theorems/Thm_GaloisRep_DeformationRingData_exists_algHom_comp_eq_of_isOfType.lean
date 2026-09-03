import Definitions.Def_GaloisRep_DeformationRingData
import P2M.Util
import P2M.Sol.S_GaloisRep_DeformationRingData_exists_algHom_comp_eq_of_isOfType

theorem GaloisRep.DeformationRingData.exists_algHom_comp_eq_of_isOfType
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hres : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (xφ : D'.R →ₐ[𝒪] A) (hxφ : IsLocalHom (xφ : D'.R →+* A))
    (h𝒟' : 𝒟' (D'.ρ.baseChangeAlong (xφ : D'.R →+* A) hxφ))
    (h𝒟₀ : 𝒟₀ (D'.ρ.baseChangeAlong (xφ : D'.R →+* A) hxφ)) :
    ∃ ψ : D₀.R →ₐ[𝒪] A, IsLocalHom (ψ : D₀.R →+* A) ∧ ψ.comp θ = xφ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_DeformationRingData_exists_algHom_comp_eq_of_isOfType.solution
