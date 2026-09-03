import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpand_jq_mem_adjoin_of_gcd_eq_one
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.qExpand_jq_mem_adjoin_of_gcd_eq_one (M : ℕ) [NeZero M] (S : Finset ℕ)
    (hSM : ∀ s ∈ S, s ∣ M) (hM : M ∈ S) (hgcd : S.gcd id = 1) (d : ℕ) [NeZero d] (hd : d ∣ M) :
    ModularCurve.qExpand ℚ d ModularCurve.jq ∈ IntermediateField.adjoin ℚ
      {x : LaurentSeries ℚ | ∃ (s : ℕ) (_ : NeZero s), s ∈ S ∧ x = ModularCurve.qExpand ℚ s ModularCurve.jq} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpand_jq_mem_adjoin_of_gcd_eq_one.solution
