import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_NumberField_pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm
attribute [-instance] LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero

set_option autoImplicit false
open NumberField M4aHerbrand M4aHerbrand.GenuineDescent LanglandsTunnell.P2.Artin

theorem NumberField.pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm
    (E F N L' : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Field N] [NumberField N]
    [Field L'] [NumberField L']
    [Algebra E F] [Algebra E N] [Algebra F N] [Algebra E L'] [Algebra L' N]
    [IsScalarTower E F N] [IsScalarTower E L' N]
    [IsGalois F N] [IsMulCommutative (N ≃ₐ[F] N)] [IsGalois E L'] [IsMulCommutative (L' ≃ₐ[E] L')]
    (hinj : Function.Injective (resHom E L' F N))
    (n' : ℕ) (hexp : ∀ g : L' ≃ₐ[E] L', g ^ n' = 1) (hn : Module.finrank E F ∣ n')
    (u : (AdeleRing (𝓞 E) E)ˣ) :
    (Units.map (genuineBaseChange E F).β.toMonoidHom u) ^ (n' / Module.finrank E F) ∈
      principalIdeles (𝓞 F) F ⊔ (genuineBaseChange F N).idelicNorm.range := by p2m_exact_reverting @_root_.P2MW.S_NumberField_pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm.solution
