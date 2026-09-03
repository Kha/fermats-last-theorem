import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_card_inertia_eq_of_isUnit
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal instTopologicallyFGOfFiniteType
attribute [-simp] AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul

set_option autoImplicit false

open scoped Pointwise
open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_card_inertia_eq_of_isUnit
    {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    {C : Type} [CommRing C] [Algebra O C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    {W₂ : Type} [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂] [IsAdicComplete (maximalIdeal W₂) W₂]
    (π : W₂) (hπ : Irreducible π) (m w : ℕ) (hm : 0 < m) (hw : 0 < w) (hwW : IsUnit (w : W₂))
    (hmW : IsUnit (m : W₂))
    [IsDomain C] [Module.Finite O C] [FaithfulSMul O C]
    {G : Type} [Group G] [Finite G] [MulSemiringAction G C] [SMulCommClass G O C] [FaithfulSMul G C]
    [Algebra.IsInvariant O C G]
    (hI : Nat.card ↥((𝔫.inertia G).subgroupOf (MulAction.stabilizer G 𝔫)) = w)
    (hIcyc : IsCyclic ↥(𝔫.inertia G))
    [Algebra.IsSeparable (O ⧸ maximalIdeal O) (C ⧸ 𝔫)]
    (eO : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W₂ (π ^ (m * w)))
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫]
    (hSdom : IsDomain (AdicCompletion (maximalIdeal S) S))
    (hSnorm : IsIntegrallyClosed (AdicCompletion (maximalIdeal S) S))
    [Algebra O S] [IsScalarTower O C S]
    (hunr : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → Algebra.IsUnramifiedAt O 𝔮) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (σ : W₂ →+* W)
      (_ : maximalIdeal W = Ideal.span {σ π})
      (e : AdicCompletion (maximalIdeal S) S ≃+* UVCrossingModel W ((σ π) ^ m)),
      ∀ (o : O) (w₀ : W₂), eO (algebraMap O (AdicCompletion (maximalIdeal O) O) o) = const (π ^ (m * w)) w₀ →
        e (algebraMap S (AdicCompletion (maximalIdeal S) S) (algebraMap O S o)) = const ((σ π) ^ m) (σ w₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_card_inertia_eq_of_isUnit.solution
