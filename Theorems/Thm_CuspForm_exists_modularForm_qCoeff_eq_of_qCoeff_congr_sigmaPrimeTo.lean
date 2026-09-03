import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_CuspForm_IntegralLattice
import P2M.Util
import P2M.Sol.S_CuspForm_exists_modularForm_qCoeff_eq_of_qCoeff_congr_sigmaPrimeTo
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve

theorem CuspForm.exists_modularForm_qCoeff_eq_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime] (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) : ∃ (F : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (aF : ℕ → ℤ), (∀ n : ℕ, (aF n : ℂ) = ModularFormClass.qCoeff F n) ∧ aF 0 = af 1 * ((p : ℤ) - 1) ∧ ∀ n : ℕ, n ≠ 0 → ((24 * m : ℕ) : ℤ) ∣ aF n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_modularForm_qCoeff_eq_of_qCoeff_congr_sigmaPrimeTo.solution
