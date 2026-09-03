import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius
import P2M.Util
namespace P2MW.S_ModularCurve_genDiffModL_U_self_inv_smul_D_of_coe_eq_coeffMap_frobenius

set_option autoImplicit false

theorem solution
    (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (S : Set ℕ) [CharP K p]
    (hC : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
      ∃ C : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K],
        ModularCurve.IsFrobPushDiff K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p C)
    (hinj : Function.Injective (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))))
    (f f' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hf' : ((f' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) =
      ModularCurve.coeffMap (frobenius K p) ((f : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K)) :
    ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM)
        (f⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) f) =
      f'⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) f' := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [ModularCurve.genDiffModL_U_self]
  apply hinj
  rw [ModularCurve.isFrobPushDiff_frobPushDiffModL hC, ModularCurve.diffQExp_smul_D,
    ModularCurve.diffQExp_smul_D]
  have hcoe : (((f⁻¹ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) = ((f : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K)⁻¹ :=
    map_inv₀ (IntermediateField.val _) f
  have hcoe' : (((f'⁻¹ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) = ((f' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K)⁻¹ :=
    map_inv₀ (IntermediateField.val _) f'
  rw [hcoe, hcoe', hf']
  exact ModularCurve.qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius K p _
