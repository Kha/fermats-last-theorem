import Mathlib.Algebra.Module.ZLattice.Summable
import P2M.Util
import P2M.Sol.S_ZLattice_summable_and_tsum_inv_norm_pow_le_of_separated

theorem ZLattice.summable_and_tsum_inv_norm_pow_le_of_separated
    {W : Type} [Fintype W] {ι : Type} {r : ℝ} (hr : 0 < r) {v : ι → W → ℝ}
    (hsep : ∀ i j, i ≠ j → r ≤ ‖v i - v j‖) (hfar : ∀ i, r ≤ ‖v i‖) {k : ℕ} (hk : Fintype.card W < k) :
    Summable (fun i => ‖v i‖⁻¹ ^ k) ∧
      ∑' i, ‖v i‖⁻¹ ^ k ≤ (3 / r) ^ k * ∑' x : Submodule.span ℤ (Set.range (Pi.basisFun ℝ W)), ‖x‖⁻¹ ^ k := by p2m_exact_reverting @_root_.P2MW.S_ZLattice_summable_and_tsum_inv_norm_pow_le_of_separated.solution
