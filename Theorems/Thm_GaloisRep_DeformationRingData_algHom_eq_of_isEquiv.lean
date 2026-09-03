import Definitions.Def_GaloisRep_DeformationRingData
import P2M.Util
import P2M.Sol.S_GaloisRep_DeformationRingData_algHom_eq_of_isEquiv

theorem GaloisRep.DeformationRingData.algHom_eq_of_isEquiv
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hA : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (ρA : GaloisRepAdic A) (hρA : 𝒟 ρA)
    (hres : ρA.residual.IsEquiv (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 A))))
    (φ₁ φ₂ : D.R →ₐ[𝒪] A) (h₁ : IsLocalHom (φ₁ : D.R →+* A)) (h₂ : IsLocalHom (φ₂ : D.R →+* A))
    (e₁ : (D.ρ.baseChangeAlong (φ₁ : D.R →+* A) h₁).IsEquiv ρA)
    (e₂ : (D.ρ.baseChangeAlong (φ₂ : D.R →+* A) h₂).IsEquiv ρA) :
    φ₁ = φ₂ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_DeformationRingData_algHom_eq_of_isEquiv.solution
