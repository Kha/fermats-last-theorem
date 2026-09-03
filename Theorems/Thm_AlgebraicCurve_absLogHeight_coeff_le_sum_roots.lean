import Definitions.Def_ModularCurve_JZeroHeightForm
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_absLogHeight_coeff_le_sum_roots

theorem AlgebraicCurve.absLogHeight_coeff_le_sum_roots {ι : Type*} (t : Finset ι)
    (α : ι → AlgebraicClosure ℚ) (m : ι → ℕ) {n : ℕ} (hdeg : ∑ i ∈ t, m i ≤ n) :
    absLogHeight (fun k : Fin (n + 1) =>
        (∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).coeff k)
      ≤ ∑ i ∈ t, (m i : ℝ) * absLogHeight ![α i, 1] + n * Real.log 2 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_absLogHeight_coeff_le_sum_roots.solution
