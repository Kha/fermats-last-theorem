import Mathlib
import Definitions.Def_ModularCurve_EichlerMass
import Theorems.Thm_ModularCurve_genusFormula_mul_expand
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_cuspCount_prime
import P2M.Util
namespace P2MW.S_ModularCurve_ssCountFormula_eq_genus
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open ModularCurve

theorem solution {N q : ℕ} (hN : N ≠ 0) (hq : q.Prime)
    (hqN : ¬ q ∣ N) :
    ssCountFormula N q = genusFormula (N * q) - 2 * genusFormula N + 1 :=
  by
    have hcop : Nat.Coprime q N := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqN
    rw [mul_comm N q, genusFormula_mul_expand hq.pos.ne' hN hcop,
      dedekindPsi_prime hq, cuspCount_prime hq]
    unfold ssCountFormula eichlerMass
    push_cast
    ring
