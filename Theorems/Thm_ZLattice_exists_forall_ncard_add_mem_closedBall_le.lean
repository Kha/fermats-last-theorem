import Mathlib.Algebra.Module.ZLattice.Summable
import P2M.Util
import P2M.Sol.S_ZLattice_exists_forall_ncard_add_mem_closedBall_le

set_option autoImplicit false

theorem ZLattice.exists_forall_ncard_add_mem_closedBall_le
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : AddSubgroup E) (hL : DiscreteTopology L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : E) (R : ℝ), 0 ≤ R →
      {x : E | x ∈ L ∧ ‖a + x‖ ≤ R}.Finite ∧
      (({x : E | x ∈ L ∧ ‖a + x‖ ≤ R}.ncard : ℕ) : ℝ) ≤ C * (1 + R) ^ Module.finrank ℝ E := by p2m_exact_reverting @_root_.P2MW.S_ZLattice_exists_forall_ncard_add_mem_closedBall_le.solution
