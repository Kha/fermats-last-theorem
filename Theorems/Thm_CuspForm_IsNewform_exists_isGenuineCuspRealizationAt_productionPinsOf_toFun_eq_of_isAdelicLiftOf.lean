import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import P2M.Util
import P2M.Sol.S_CuspForm_IsNewform_exists_isGenuineCuspRealizationAt_productionPinsOf_toFun_eq_of_isAdelicLiftOf
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain AutomorphicForm
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem CuspForm.IsNewform.exists_isGenuineCuspRealizationAt_productionPinsOf_toFun_eq_of_isAdelicLiftOf
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ AdelicDock.ratLevel M) :
    ∃ (Θ : HeckeEigensystem ℚ ℂ)
      (R : SmoothCuspRealizationAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        Θ.toRawCentral),
      IsGenuineCuspRealizationAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        Θ.toRawCentral R ∧
      R.toFun = Φ ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → Θ.a v = ModularFormClass.qCoeff g (Ideal.absNorm v.asIdeal)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → Θ.b v = (Ideal.absNorm v.asIdeal : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNewform_exists_isGenuineCuspRealizationAt_productionPinsOf_toFun_eq_of_isAdelicLiftOf.solution
