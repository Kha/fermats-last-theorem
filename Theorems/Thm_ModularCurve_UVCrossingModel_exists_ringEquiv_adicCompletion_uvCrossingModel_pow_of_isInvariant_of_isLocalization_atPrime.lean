import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_isLocalization_atPrime
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal instTopologicallyFGOfFiniteType
attribute [-simp] AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul

set_option autoImplicit false

open scoped Pointwise TensorProduct
open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_isLocalization_atPrime
    {A₂ A₁ : Type} [CommRing A₂] [CommRing A₁] [IsNoetherianRing A₂] [IsNoetherianRing A₁] [IsDomain A₁]
    [Algebra A₂ A₁] [Module.Finite A₂ A₁] [FaithfulSMul A₂ A₁]
    {G : Type} [Group G] [Fintype G] [MulSemiringAction G A₁] [SMulCommClass G A₂ A₁] [FaithfulSMul G A₁]
    [Algebra.IsInvariant A₂ A₁ G]
    (y : Ideal A₁) [y.IsMaximal] (𝔭 : Ideal A₂) [𝔭.IsPrime] (h𝔭 : y.comap (algebraMap A₂ A₁) = 𝔭)
    {W₂ : Type} [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂] [IsAdicComplete (maximalIdeal W₂) W₂]
    (π : W₂) (hπ : Irreducible π) (m w : ℕ) (hm : 0 < m) (hw : 0 < w) (hwW : IsUnit (w : W₂))
    (hmW : IsUnit (m : W₂))
    (hIy : Nat.card ↥(y.inertia G) = w) (hIcyc : IsCyclic ↥(y.inertia G))
    (O : Type) [CommRing O] [IsLocalRing O] [Algebra A₂ O] [IsLocalization.AtPrime O 𝔭]
    (eO : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W₂ (π ^ (m * w)))
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra A₁ S] [IsLocalization.AtPrime S y]
    (hSdom : IsDomain (AdicCompletion (maximalIdeal S) S))
    (hSnorm : IsIntegrallyClosed (AdicCompletion (maximalIdeal S) S))

    (hunr : letI : Algebra A₂ S := ((algebraMap A₁ S).comp (algebraMap A₂ A₁)).toAlgebra
      ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → Algebra.IsUnramifiedAt A₂ 𝔮)

    (hsep : ∀ h : 𝔭 ≤ y.comap (algebraMap A₂ A₁),
      letI : Algebra (A₂ ⧸ 𝔭) (A₁ ⧸ y) := Ideal.Quotient.algebraQuotientOfLEComap h
      Algebra.IsSeparable (A₂ ⧸ 𝔭) (A₁ ⧸ y)) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (σ : W₂ →+* W)
      (_ : maximalIdeal W = Ideal.span {σ π})
      (e : AdicCompletion (maximalIdeal S) S ≃+* UVCrossingModel W ((σ π) ^ m)),
      ∀ (b : A₂) (w₀ : W₂), eO (algebraMap O (AdicCompletion (maximalIdeal O) O) (algebraMap A₂ O b)) = const (π ^ (m * w)) w₀ →
        e (algebraMap S (AdicCompletion (maximalIdeal S) S) (algebraMap A₁ S (algebraMap A₂ A₁ b))) = const ((σ π) ^ m) (σ w₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_isLocalization_atPrime.solution
