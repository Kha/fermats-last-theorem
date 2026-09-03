import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import P2M.Util
namespace P2MW.S_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldC_mul
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

theorem solution
    (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hpN : ¬ p ∣ N) (hpℓ : p ≠ ℓ) :
    ModularCurve.charLDegeneracyRoof κ N ℓ = ModularCurve.modularFunctionFieldC κ (N * ℓ) := by
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hpNℓ : ¬ p ∣ N * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h2
    · exact hpN h1
    · exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 h2)
  apply le_antisymm
  ·
    rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC κ p (N * ℓ) hpNℓ]
    unfold ModularCurve.charLDegeneracyRoof
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ModularCurve.jqModC_mem_full κ (N * ℓ)
    · exact ModularCurve.jqModCd_mem_full κ (N * ℓ) (dvd_mul_right N ℓ)
    · exact ModularCurve.jqModCd_mem_full κ (N * ℓ) (dvd_mul_left ℓ N)
    · exact ModularCurve.jqModCd_mem_full κ (N * ℓ) dvd_rfl
  ·
    unfold ModularCurve.modularFunctionFieldC ModularCurve.charLDegeneracyRoof
    apply IntermediateField.adjoin.mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr rfl))

#print axioms solution
