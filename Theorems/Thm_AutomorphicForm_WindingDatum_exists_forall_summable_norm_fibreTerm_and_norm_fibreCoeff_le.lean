import Mathlib
import Definitions.Def_AutomorphicForm_WindingDatum
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WindingDatum_exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le

theorem AutomorphicForm.WindingDatum.exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le
    {r d c : ℕ} (𝒟 : AutomorphicForm.WindingDatum r d c) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ (i : ℕ) (n : Fin d → ℤ),
        Summable (fun γ : 𝒟.sub i => ‖𝒟.fibreTerm i n γ‖) ∧
        ∑' γ : 𝒟.sub i, ‖𝒟.fibreTerm i n γ‖ ≤ K * 𝒟.C i ∧
        ‖𝒟.fibreCoeff i n‖ ≤ K * 𝒟.C i) ∧
      ∀ n : Fin d → ℤ, Summable fun i : ℕ => ‖𝒟.lam i * 𝒟.fibreCoeff i n‖ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WindingDatum_exists_forall_summable_norm_fibreTerm_and_norm_fibreCoeff_le.solution
