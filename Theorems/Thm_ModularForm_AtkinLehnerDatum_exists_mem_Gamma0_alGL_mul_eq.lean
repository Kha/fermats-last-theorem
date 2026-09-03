import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq

open scoped MatrixGroups
theorem ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 M ∧
      W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ g = Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq.solution
