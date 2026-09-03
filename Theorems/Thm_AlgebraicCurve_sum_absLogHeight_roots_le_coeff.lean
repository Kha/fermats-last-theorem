import Definitions.Def_ModularCurve_JZeroHeightForm
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_sum_absLogHeight_roots_le_coeff

theorem AlgebraicCurve.sum_absLogHeight_roots_le_coeff {ι : Type*} (t : Finset ι)
    (α : ι → AlgebraicClosure ℚ) (m : ι → ℕ) {n : ℕ} (hdeg : ∑ i ∈ t, m i ≤ n) :
    ∑ i ∈ t, (m i : ℝ) * absLogHeight ![α i, 1]
      ≤ absLogHeight (fun k : Fin (n + 1) =>
          (∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).coeff k)
        + Real.log (Real.sqrt (n + 1)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_sum_absLogHeight_roots_le_coeff.solution
