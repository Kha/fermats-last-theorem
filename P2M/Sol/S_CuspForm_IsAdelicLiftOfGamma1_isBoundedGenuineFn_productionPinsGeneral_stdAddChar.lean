import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_AdelicTraceProducer
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_continuous
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_isKfSmooth
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_exists_forall_norm_le
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_contDiff_two_unipotentGL2_ratArchLine_mul
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_apply_unipotentGL2_algebraMap_mul
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import P2M.Util
namespace P2MW.S_CuspForm_IsAdelicLiftOfGamma1_isBoundedGenuineFn_productionPinsGeneral_stdAddChar

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.StandardAddChar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem solution
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    IsBoundedGenuineFn ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) Φ := by
  have hW := AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff
    (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
    (stdAddChar ℚ) (isGlobalAddChar_stdAddChar ℚ) Φ
    (fun β g => hΦ.apply_unipotentGL2_algebraMap_mul β g) hΦ.isKfSmooth
    (fun g => hΦ.contDiff_two_unipotentGL2_ratArchLine_mul g)
  obtain ⟨C, hC⟩ := hΦ.exists_forall_norm_le
  refine ⟨hΦ.continuous, ?_, hW.1, hW.2⟩
  intro c u d₁ d₂ T _ _
  exact ⟨C, fun g _ => hC g⟩
