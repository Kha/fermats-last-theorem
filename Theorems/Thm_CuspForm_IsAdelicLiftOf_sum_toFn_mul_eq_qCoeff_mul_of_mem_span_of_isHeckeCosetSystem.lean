import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOf_sum_toFn_mul_eq_qCoeff_mul_of_mem_span_of_isHeckeCosetSystem
attribute [-instance] HeckeIntegralSeam.finite_padicInt_quotient_span_p
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.sum_toFn_mul_eq_qCoeff_mul_of_mem_span_of_isHeckeCosetSystem
    {M' : ℕ} [NeZero M'] (q : ℕ) [Fact q.Prime]
    {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2} (hg : g.IsNormalizedEigenform)
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (y : LocalNewvector.AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ q ^ 2 * M')
    (reps : Fin (Ideal.absNorm (@AdelicDock.padicPlace ℓ ⟨hℓ⟩).asIdeal + 1) → AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ)
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem
      (NumberField.AdelicLevel.levelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel (q ^ 2 * M')) ⊓
        AutomorphicForm.finiteAdelicGL2Subgroup ℚ)
      (NumberField.AdelicLevel.heckeGen (NumberField.RingOfIntegers ℚ) ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) reps)
    (hpure : ∀ j, ∃ m : GL (Fin 2) ((@AdelicDock.padicPlace ℓ ⟨hℓ⟩).adicCompletion ℚ),
      reps j = AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩) m))
    (z : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    ∑ j, (LocalNewvector.AdelicSpan.toFn Φ y).toFn (z * reps j) =
      (ModularFormClass.qCoeff g ℓ : ℂ) * (LocalNewvector.AdelicSpan.toFn Φ y).toFn z := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_sum_toFn_mul_eq_qCoeff_mul_of_mem_span_of_isHeckeCosetSystem.solution
