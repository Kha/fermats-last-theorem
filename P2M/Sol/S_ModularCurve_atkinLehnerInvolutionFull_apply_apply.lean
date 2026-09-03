import Mathlib
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_modularFunctionFieldFull_algHom_ext
import P2M.Util
namespace P2MW.S_ModularCurve_atkinLehnerInvolutionFull_apply_apply
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve

theorem solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hpN : ¬ p ∣ N) (x : modularFunctionFieldFull (N * p)) :
    atkinLehnerInvolutionFull N p (atkinLehnerInvolutionFull N p x) = x := by
  have hσ : IsAtkinLehnerAutFull N p (atkinLehnerInvolutionFull N p) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N p
      (ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N p Fact.out hpN)
  suffices h : (atkinLehnerInvolutionFull N p).toAlgHom.comp (atkinLehnerInvolutionFull N p).toAlgHom
      = AlgHom.id ℚ _ from
    AlgHom.congr_fun h x
  refine ModularCurve.modularFunctionFieldFull_algHom_ext fun d hd0 hd => ?_
  rw [AlgHom.comp_apply, AlgHom.id_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.toAlgHom_apply]
  by_cases hpd : p ∣ d
  ·
    obtain ⟨e, rfl⟩ := hpd
    haveI : NeZero e := ⟨fun h => NeZero.ne (p * e) (by rw [h, mul_zero])⟩
    have heN : e ∣ N := by
      have h1 : e * p ∣ N * p := by rwa [mul_comm e p]
      exact Nat.dvd_of_mul_dvd_mul_right (Fact.out : p.Prime).pos h1
    obtain ⟨h1, h2⟩ := hσ e inferInstance heN
    have hel : (⟨qExpand ℚ (p * e) jq, jqd_mem_full (N * p) hd⟩ : modularFunctionFieldFull (N * p)) =
        ⟨qExpand ℚ (e * p) jq, jqd_mem_full (N * p) (Nat.mul_dvd_mul_right heN p)⟩ :=
      Subtype.ext (qExpand_congr (mul_comm p e) jq)
    rw [hel, h2, h1]
  ·
    have hdN : d ∣ N :=
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpd).symm.dvd_of_dvd_mul_right hd
    obtain ⟨h1, h2⟩ := hσ d hd0 hdN
    have hel : (⟨qExpand ℚ d jq, jqd_mem_full (N * p) hd⟩ : modularFunctionFieldFull (N * p)) =
        ⟨qExpand ℚ d jq, jqd_mem_full (N * p) (Dvd.dvd.mul_right hdN p)⟩ := rfl
    rw [hel, h1, h2]
