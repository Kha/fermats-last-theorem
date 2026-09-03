import Mathlib
import Definitions.Def_GaloisRep_DeformationRingData
import P2M.Util
import P2M.Sol.S_GaloisRep_DeformationRingData_comp_subtype_ker_mapCotangent_eq_zero_of_isOfType_lift

set_option autoImplicit false
theorem GaloisRep.DeformationRingData.comp_subtype_ker_mapCotangent_eq_zero_of_isOfType_lift
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective θ) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (S : Type) [CommRing S] [Algebra 𝒪 S] [IsLocalRing (TrivSqZeroExt S S)]
    [IsNoetherianRing (TrivSqZeroExt S S)]
    [IsAdicComplete (IsLocalRing.maximalIdeal (TrivSqZeroExt S S)) (TrivSqZeroExt S S)]
    [IsLocalHom (algebraMap 𝒪 (TrivSqZeroExt S S))]
    (hres : Function.Surjective
      (IsLocalRing.residue (TrivSqZeroExt S S) ∘ algebraMap 𝒪 (TrivSqZeroExt S S)))
    (φ : (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪] S)
    (ψ : D'.R →ₐ[𝒪] TrivSqZeroExt S S) (hψ : IsLocalHom (ψ : D'.R →+* TrivSqZeroExt S S))
    (hsnd : ∀ (r : D'.R) (hr : r ∈ RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)),
      (ψ r).snd = φ ((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).toCotangent ⟨r, hr⟩))
    (h𝒟' : 𝒟' (D'.ρ.baseChangeAlong (ψ : D'.R →+* TrivSqZeroExt S S) hψ))
    (h𝒟₀ : 𝒟₀ (D'.ρ.baseChangeAlong (ψ : D'.R →+* TrivSqZeroExt S S) hψ)) :
    φ ∘ₗ (LinearMap.ker (Ideal.mapCotangent (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪))
        (RingHom.ker x₀) θ (fun _ hr => hr))).subtype = 0 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_DeformationRingData_comp_subtype_ker_mapCotangent_eq_zero_of_isOfType_lift.solution
