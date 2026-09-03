import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne

set_option autoImplicit false

theorem WeierstrassCurve.exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne
    (k : Type) [Field k] (E₀ : WeierstrassCurve k) [E₀.IsElliptic]
    (E₁ : WeierstrassCurve (DualNumber k)) (hE₁ : E₁.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀)
    (hE₁' : ∀ C : WeierstrassCurve.VariableChange (DualNumber k),
      C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 → C • (E₀.map (algebraMap k (DualNumber k))) ≠ E₁)
    (E : WeierstrassCurve (DualNumber k)) (hE : E.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀) :
    ∃ (c : k) (C : WeierstrassCurve.VariableChange (DualNumber k)),
      C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 ∧
      C • (E₁.map (TrivSqZeroExt.map (c • LinearMap.id : k →ₗ[k] k)).toRingHom) = E := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne.solution
