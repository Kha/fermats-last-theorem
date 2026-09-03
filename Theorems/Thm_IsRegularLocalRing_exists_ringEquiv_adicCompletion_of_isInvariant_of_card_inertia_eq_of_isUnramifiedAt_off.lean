import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_exists_ringEquiv_adicCompletion_of_isInvariant_of_card_inertia_eq_of_isUnramifiedAt_off
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open Polynomial open IsLocalRing hiding ringKrullDim_adicCompletion_maximalIdeal_eq

open scoped Pointwise

theorem IsRegularLocalRing.exists_ringEquiv_adicCompletion_of_isInvariant_of_card_inertia_eq_of_isUnramifiedAt_off
    {O : Type} [CommRing O] [IsRegularLocalRing O]
    (ϖ s : O) (hmaxO : maximalIdeal O = Ideal.span {ϖ, s}) (hdimO : ringKrullDim O = 2)
    (e : ℕ) (he : 0 < e) (heO : IsUnit (e : O))
    {C : Type} [CommRing C] [Algebra O C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    [IsDomain C] [Module.Finite O C] [FaithfulSMul O C]
    {G : Type} [Group G] [Finite G] [MulSemiringAction G C] [SMulCommClass G O C] [FaithfulSMul G C]
    [Algebra.IsInvariant O C G]
    (hI : Nat.card ↥((𝔫.inertia G).subgroupOf (MulAction.stabilizer G 𝔫)) = e)
    (hIcyc : IsCyclic ↥(𝔫.inertia G))
    [Algebra.IsSeparable (O ⧸ maximalIdeal O) (C ⧸ 𝔫)]
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫]
    (hSdom : IsDomain (AdicCompletion (maximalIdeal S) S))
    (hSnorm : IsIntegrallyClosed (AdicCompletion (maximalIdeal S) S))
    [Algebra O S] [IsScalarTower O C S]

    (hunr : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal →
      s ∉ 𝔮.comap (algebraMap O S) → Algebra.IsUnramifiedAt O 𝔮) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsRegularLocalRing R') (ϖ' τ : R')
      (_ : maximalIdeal R' = Ideal.span {ϖ', τ}) (_ : ringKrullDim R' = 2)
      (ι : AdicCompletion (maximalIdeal S) S ≃+* AdicCompletion (maximalIdeal R') R'),
      ι (algebraMap S (AdicCompletion (maximalIdeal S) S) (algebraMap O S ϖ)) =
        algebraMap R' (AdicCompletion (maximalIdeal R') R') ϖ' := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_exists_ringEquiv_adicCompletion_of_isInvariant_of_card_inertia_eq_of_isUnramifiedAt_off.solution
