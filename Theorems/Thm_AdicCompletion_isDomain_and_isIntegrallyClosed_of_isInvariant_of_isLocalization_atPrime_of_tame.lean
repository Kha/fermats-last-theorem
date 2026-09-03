import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_isDomain_and_isIntegrallyClosed_of_isInvariant_of_isLocalization_atPrime_of_tame
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul

set_option autoImplicit false

open IsLocalRing hiding isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing

theorem AdicCompletion.isDomain_and_isIntegrallyClosed_of_isInvariant_of_isLocalization_atPrime_of_tame
    {A₂ A₁ : Type} [CommRing A₂] [CommRing A₁] [IsNoetherianRing A₂] [IsNoetherianRing A₁] [IsDomain A₁] [IsIntegrallyClosed A₁]
    [Algebra A₂ A₁] [Module.Finite A₂ A₁] [FaithfulSMul A₂ A₁]
    {G : Type} [Group G] [Fintype G] [MulSemiringAction G A₁] [SMulCommClass G A₂ A₁] [FaithfulSMul G A₁]
    [Algebra.IsInvariant A₂ A₁ G]
    (y : Ideal A₁) [y.IsMaximal] (𝔭 : Ideal A₂) [𝔭.IsPrime] (h𝔭 : y.comap (algebraMap A₂ A₁) = 𝔭)
    (e : ℕ) (he : 0 < e)
    (hIy : Nat.card ↥(y.inertia G) = e) (hIcyc : IsCyclic ↥(y.inertia G))
    (𝔔₀ : Ideal A₂) [𝔔₀.IsPrime] (h𝔔₀ : 𝔔₀ ≤ 𝔭) (ϖ : A₂)
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [Algebra A₂ O] [IsLocalization.AtPrime O 𝔭]
    (s : O) (hsO : 𝔔₀.map (algebraMap A₂ O) = Ideal.span {s})
    (hmaxO : maximalIdeal O = Ideal.span {algebraMap A₂ O ϖ, s}) (hdimO : ringKrullDim O = 2)
    (heO : IsUnit (e : O))

    (hunr : ∀ (𝔔 : Ideal A₁) [𝔔.IsPrime], 𝔔 ≤ y → 𝔔.height = 1 → 𝔔.comap (algebraMap A₂ A₁) ≠ 𝔔₀ →
      Algebra.IsUnramifiedAt A₂ 𝔔)

    (hsep : ∀ h : 𝔭 ≤ y.comap (algebraMap A₂ A₁),
      letI : Algebra (A₂ ⧸ 𝔭) (A₁ ⧸ y) := Ideal.Quotient.algebraQuotientOfLEComap h
      Algebra.IsSeparable (A₂ ⧸ 𝔭) (A₁ ⧸ y)) :
    ∀ (S : Type) [CommRing S] [IsLocalRing S] [Algebra A₁ S] [IsLocalization.AtPrime S y],
      IsDomain (AdicCompletion (maximalIdeal S) S) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal S) S) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_isDomain_and_isIntegrallyClosed_of_isInvariant_of_isLocalization_atPrime_of_tame.solution
