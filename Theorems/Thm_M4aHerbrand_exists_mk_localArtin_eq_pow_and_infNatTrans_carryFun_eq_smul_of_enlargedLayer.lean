import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_M4aHerbrand_exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer
attribute [-instance] LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin open groupCohomology hiding carryFun_mem_cocycles2 open M4aHerbrand hiding idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem M4aHerbrand.exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer
    (E F F' K : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F'] [Field K] [NumberField K]
    [Algebra E F] [Algebra E F'] [Algebra F K] [Algebra F' K] [Algebra E K] [IsScalarTower E F K] [IsScalarTower E F' K]
    [IsGalois E K] [IsGalois E F] [IsGalois E F'] [IsMulCommutative (K ≃ₐ[E] K)]

    (hgen : ∀ x : K, x ∈ Algebra.adjoin E (Set.range (algebraMap F K) ∪ Set.range (algebraMap F' K)))

    (v : HeightOneSpectrum (𝓞 E)) (wK : HeightOneSpectrum (𝓞 K)) (hv : wK.under (𝓞 E) = v)
    [IsMulCommutative ↥(NumberField.PlaceDecomp.decomp E K wK)]

    (ρ : ↥(NumberField.PlaceDecomp.decomp E K wK) →* ↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))))
    (hρres : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E K wK), ((ρ σ : ↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) : F ≃ₐ[E] F) =
      AlgEquiv.restrictNormalHom F (σ : K ≃ₐ[E] K))
    (ρ' : ↥(NumberField.PlaceDecomp.decomp E K wK) →* ↥(NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))))
    (hρ'surj : Function.Surjective ρ')
    (hρ'res : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E K wK), ((ρ' σ : ↥(NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F')))) : F' ≃ₐ[E] F') =
      AlgEquiv.restrictNormalHom F' (σ : K ≃ₐ[E] K))
    (hρ'ker : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E K wK), ρ' σ = 1 ↔ ∀ x : F', (σ : K ≃ₐ[E] K) (algebraMap F' K x) = algebraMap F' K x)
    (hρ'lift : ∀ τ : ↥(NumberField.PlaceDecomp.decomp F' K wK), ∃ σ : ↥(NumberField.PlaceDecomp.decomp E K wK),
      (σ : K ≃ₐ[E] K) = AlgEquiv.restrictScalars E (τ : K ≃ₐ[F'] K) ∧ ρ' σ = 1)
    (he' : ((wK.under (𝓞 F')).under (𝓞 E)).asIdeal.ramificationIdx' (wK.under (𝓞 F')).asIdeal = 1)
    (hdvd' : Nat.card ↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))) ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F' (wK.under (𝓞 F'))))

    (q : ℕ) [Fact q.Prime] (L2 : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L2]
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E K wK) L2] [FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E K wK) L2]
    [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ]
    (Φ2 : wK.adicCompletion K ≃+* L2)
    (hΦ21 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K wK)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L2 y = algebraMap ℚ_[q] L2 y)
    (hΦ22 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K wK)) (y : (↥L2)ˣ), ((g • y : (↥L2)ˣ) : L2) = g • (y : L2))
    (hΦ23 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K wK)) (y : wK.adicCompletion K), Φ2 (g • y) = g • Φ2 y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (hbase2 : ExtCitation.LocalLevel.IsBase q L2 ↥(NumberField.PlaceDecomp.decomp E K wK) K₀)
    (u2 : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ))
    (hu2 : ExtCitation.LocalLevel.IsLocalFundamentalClass q L2 ↥(NumberField.PlaceDecomp.decomp E K wK) K₀ u2)

    (𝔣K : Ideal (𝓞 E)) (hadmK : NumberField.NormIndex.IsAdmissibleModulusOfDegree E K (Module.finrank E K) 𝔣K)
    (rK : (AdeleRing (𝓞 E) E)ˣ →* (K ≃ₐ[E] K))
    (hrK₁ : principalIdeles (𝓞 E) E ≤ rK.ker)
    (hrK₂ : rK.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E K).idelicNorm.range)
    (hrK₃ : Function.Surjective rK)
    (hrK₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣K u 1 →
      rK u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E K v ^ placeOrd E (projFin E u) v)

    (ιv : (v.adicCompletion E)ˣ →* (AdeleRing (𝓞 E) E)ˣ)
    (hιv : ∀ z, ιv z ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hιv' : ∀ z, finPart v (ιv z) = z)
    (fE : (v.adicCompletion E)ˣ →* ↥(NumberField.PlaceDecomp.decomp E K wK))
    (hfE : ∀ z, ((fE z : ↥(NumberField.PlaceDecomp.decomp E K wK)) : K ≃ₐ[E] K) = rK (ιv z))

    (t : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ ρ.ker) (ht : ∀ c, c ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (a : (v.adicCompletion E)ˣ) (b2 : (↥L2)ˣ)
    (hb2 : ((b2 : ↥L2) : PadicAlgCl q) =
      ((Φ2 (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E K (⟨wK, hv⟩ : v.Extension (𝓞 K))
        (a : v.adicCompletion E)) : ↥L2) : PadicAlgCl q))
    (hb2inv : (Additive.ofMul b2 : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ) ∈
      Representation.invariants ((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).ρ.comp (ρ.ker).subtype))
    (hca : carryFun t ht htfin (A := (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).quotientToInvariants (ρ.ker))
        ⟨Additive.ofMul b2, hb2inv⟩ ∈
      cocycles₂ ((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).quotientToInvariants (ρ.ker))) :
    ∃ m : ℕ, (QuotientGroup.mk (fE a) : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ ρ.ker) = t ^ m ∧
      ((infNatTrans ℤ (ρ.ker) 2).app (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ)).hom
          ((H2π ((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).quotientToInvariants (ρ.ker))).hom
            ⟨carryFun t ht htfin (A := (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ).quotientToInvariants (ρ.ker))
              ⟨Additive.ofMul b2, hb2inv⟩, hca⟩) =
        (m * Nat.card (ρ.ker)) • u2 := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer.solution
