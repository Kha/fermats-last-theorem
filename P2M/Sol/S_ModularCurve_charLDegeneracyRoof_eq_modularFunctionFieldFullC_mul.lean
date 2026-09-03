import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import P2M.Util
namespace P2MW.S_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
open ModularCurve
set_option autoImplicit false

theorem solution
    (k : Type*) [Field k]
    (ℓ : ℕ) [CharP k ℓ]
    (N : ℕ) [NeZero N] (q : ℕ) [NeZero q] [NeZero (N * q)]
    (hℓNq : ¬ ℓ ∣ N * q) :
    charLDegeneracyRoof k N q = modularFunctionFieldFullC k (N * q) := by
  apply le_antisymm
  ·
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact jqModC_mem_full k (N * q)
    · exact jqModCd_mem_full k (N * q) (dvd_mul_right N q)
    · exact jqModCd_mem_full k (N * q) (dvd_mul_left q N)
    · exact jqModCd_mem_full k (N * q) dvd_rfl
  ·
    rw [← modularFunctionFieldC_eq_modularFunctionFieldFullC k ℓ (N * q) hℓNq]
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact IntermediateField.subset_adjoin _ _ (Or.inl rfl)
    · exact IntermediateField.subset_adjoin _ _ (Or.inr (Or.inr (Or.inr rfl)))
