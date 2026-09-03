import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul

open scoped MatrixGroups ModularForm in

theorem ModularForm.exists_weight_one_gamma1_three_slash_fricke_eq_smul :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma1 3 : Subgroup (GL (Fin 2) ℝ)) 1,
      (∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 g).coeff n = (r : ℂ)) ∧
      (UpperHalfPlane.qExpansion 1 g).coeff 0 = 1 ∧
      ∀ W : GL (Fin 2) ℝ, (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; 3, 0] →
        (⇑g : UpperHalfPlane → ℂ) ∣[(1 : ℤ)] W =
          (-Complex.I / (Real.sqrt 3 : ℂ)) • (⇑g : UpperHalfPlane → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.solution
