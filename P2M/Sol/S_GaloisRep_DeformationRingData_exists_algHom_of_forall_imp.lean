import Definitions.Def_GaloisRep_DeformationRingData
import P2M.Util
namespace P2MW.S_GaloisRep_DeformationRingData_exists_algHom_of_forall_imp

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A],
      GaloisRepAdic A → Prop}
    (h : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
      (ρ : GaloisRepAdic A), 𝒟₀ ρ → 𝒟' ρ)
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀)
    (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟') :
    ∃ θ : D'.R →ₐ[𝒪] D₀.R, ∃ hθ : IsLocalHom (θ : D'.R →+* D₀.R),
      (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ := by
  obtain ⟨θ, hθ, -⟩ :=
    D'.universal D₀.R D₀.residue_surjective D₀.ρ (h D₀.ρ D₀.isOfType) D₀.residual_isEquiv
  exact ⟨θ, hθ⟩

#print axioms solution
