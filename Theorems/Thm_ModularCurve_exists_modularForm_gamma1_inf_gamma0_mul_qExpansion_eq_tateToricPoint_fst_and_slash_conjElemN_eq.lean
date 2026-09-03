import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_eq_tateToricPoint_fst_and_slash_conjElemN_eq
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_eq_tateToricPoint_fst_and_slash_conjElemN_eq
    (N n : ℕ) [NeZero N] [NeZero n] :
    ∃ X : ℂˣ → ModularForm ((CongruenceSubgroup.Gamma1 n ⊓ CongruenceSubgroup.Gamma0 (N * n) :
        Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2,
      (∀ c : ℂˣ, c ^ n = 1 → c ≠ 1 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(X c))) =
          (ModularCurve.tateToricPoint ℂ N c).1 + HahnSeries.C ((12 : ℂ)⁻¹)) ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 n → ∀ c : ℂˣ, c ^ n = 1 → c ≠ 1 →
        (⇑(X c) ∣[(2 : ℤ)] ModularCurve.FullLevel.conjElemN N ρ) = ⇑(X (c ^ ((ρ 1 1 : ℤ))))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_eq_tateToricPoint_fst_and_slash_conjElemN_eq.solution
