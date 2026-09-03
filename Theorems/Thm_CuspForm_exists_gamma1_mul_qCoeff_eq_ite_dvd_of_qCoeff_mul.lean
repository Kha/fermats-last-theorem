import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gamma1_mul_qCoeff_eq_ite_dvd_of_qCoeff_mul
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

theorem CuspForm.exists_gamma1_mul_qCoeff_eq_ite_dvd_of_qCoeff_mul
    (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (q : ℕ) (hq : q ≠ 0)
    (hfU : ∀ n : ℕ, ModularFormClass.qCoeff f (q * n) =
      ModularFormClass.qCoeff f q * ModularFormClass.qCoeff f n) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 (N * q)) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if q ∣ n then 0 else ModularFormClass.qCoeff f n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gamma1_mul_qCoeff_eq_ite_dvd_of_qCoeff_mul.solution
