import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_map_eq_and_forall_variableChange_smul_map_ne

set_option autoImplicit false

theorem WeierstrassCurve.exists_map_eq_and_forall_variableChange_smul_map_ne
    (k : Type*) [Field k] (E₀ : WeierstrassCurve k) :
    ∃ E₁ : WeierstrassCurve (DualNumber k), E₁.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀ ∧
      ∀ C : WeierstrassCurve.VariableChange (DualNumber k),
        C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 →
          C • (E₀.map (algebraMap k (DualNumber k))) ≠ E₁ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_map_eq_and_forall_variableChange_smul_map_ne.solution
