import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentSeries_injective_of_forall_apply_tmul_eq_smul_map

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem LaurentSeries.injective_of_forall_apply_tmul_eq_smul_map
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (Φ : K ⊗[k] LaurentSeries k →ₗ[k] LaurentSeries K)
    (hΦ : ∀ (a : K) (f : LaurentSeries k), Φ (a ⊗ₜ[k] f) = a • f.map (algebraMap k K)) :
    Function.Injective Φ := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_injective_of_forall_apply_tmul_eq_smul_map.solution
