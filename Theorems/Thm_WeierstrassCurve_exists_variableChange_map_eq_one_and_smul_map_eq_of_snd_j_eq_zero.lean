import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_map_eq_one_and_smul_map_eq_of_snd_j_eq_zero

set_option autoImplicit false

theorem WeierstrassCurve.exists_variableChange_map_eq_one_and_smul_map_eq_of_snd_j_eq_zero
    (k : Type) [Field k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hj0 : E₀.j ≠ 0) (hj1728 : E₀.j ≠ 1728)
    (E : WeierstrassCurve (DualNumber k)) [E.IsElliptic]
    (hE : E.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀)
    (hj : TrivSqZeroExt.snd E.j = 0) :
    ∃ C : WeierstrassCurve.VariableChange (DualNumber k),
      C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 ∧
      C • (E₀.map (algebraMap k (DualNumber k))) = E := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_map_eq_one_and_smul_map_eq_of_snd_j_eq_zero.solution
