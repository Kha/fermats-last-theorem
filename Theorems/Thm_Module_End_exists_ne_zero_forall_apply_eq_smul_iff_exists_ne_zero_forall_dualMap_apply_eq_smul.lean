import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul

set_option autoImplicit false

theorem Module.End.exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} (T : ι → Module.End K V) (hT : ∀ i j, Commute (T i) (T j)) (μ : ι → K) :
    (∃ v : V, v ≠ 0 ∧ ∀ i, T i v = μ i • v) ↔
      ∃ φ : Module.Dual K V, φ ≠ 0 ∧ ∀ i, (T i).dualMap φ = μ i • φ := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_ne_zero_forall_apply_eq_smul_iff_exists_ne_zero_forall_dualMap_apply_eq_smul.solution
