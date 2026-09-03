import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_map_frobenius_dualNumber_eq_map_map_map

set_option autoImplicit false

theorem WeierstrassCurve.map_frobenius_dualNumber_eq_map_map_map
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] [CharP (DualNumber k) q]
    (W : WeierstrassCurve (DualNumber k)) :
    W.map (frobenius (DualNumber k) q) =
      ((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (frobenius k q)).map (algebraMap k (DualNumber k)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_map_frobenius_dualNumber_eq_map_map_map.solution
