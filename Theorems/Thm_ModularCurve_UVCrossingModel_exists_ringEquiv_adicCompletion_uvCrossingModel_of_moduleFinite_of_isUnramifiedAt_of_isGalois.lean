import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adicCompletion_uvCrossingModel_of_moduleFinite_of_isUnramifiedAt_of_isGalois
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open ModularCurve open ModularCurve.UVCrossingModel hiding exists_ringEquiv_uvCrossingModel_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue
open scoped TensorProduct

theorem ModularCurve.UVCrossingModel.exists_ringEquiv_adicCompletion_uvCrossingModel_of_moduleFinite_of_isUnramifiedAt_of_isGalois
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hμ : ∃ ζ : W, IsPrimitiveRoot ζ n)
    (Sb S : Type*) [CommRing Sb] [CommRing S] [IsNoetherianRing Sb] [IsNoetherianRing S]
    [IsLocalRing Sb] [IsLocalRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra Sb S] [Module.Finite Sb S] (hinj : Function.Injective (algebraMap Sb S))
    (hdimS : ringKrullDim S ≤ (2 : WithBot ℕ∞)) (hdimS' : 2 ≤ ringKrullDim S) (hdimSb : 2 ≤ ringKrullDim Sb)
    (t : S) (ht : t ∈ IsLocalRing.maximalIdeal S) (ht0 : t ≠ 0)
    (hunrS : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → Algebra.IsUnramifiedAt Sb 𝔮)
    (hresS : ∀ s : S, ∃ r : Sb, s - algebraMap Sb S r ∈ IsLocalRing.maximalIdeal S)
    (eb : (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) ≃+* UVCrossingModel W (π ^ n))
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra Sb K₁] [IsFractionRing Sb K₁]
    [Algebra S K] [IsFractionRing S K] [Algebra K₁ K] [Algebra Sb K]
    [IsScalarTower Sb S K] [IsScalarTower Sb K₁ K] [FiniteDimensional K₁ K] [IsGalois K₁ K]
    (hcycK : IsCyclic (K ≃ₐ[K₁] K)) (hdegK : Module.finrank K₁ K = n) :
    ∃ e : (AdicCompletion (IsLocalRing.maximalIdeal S) S) ≃+* UVCrossingModel W π,
      ∀ (x : Sb) (w : W), eb (algebraMap Sb (AdicCompletion (IsLocalRing.maximalIdeal Sb) Sb) x) = const (π ^ n) w →
        e (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap Sb S x)) = const π w := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adicCompletion_uvCrossingModel_of_moduleFinite_of_isUnramifiedAt_of_isGalois.solution
