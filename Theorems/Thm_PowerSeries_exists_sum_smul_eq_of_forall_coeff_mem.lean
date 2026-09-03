import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem

set_option autoImplicit false

theorem PowerSeries.exists_sum_smul_eq_of_forall_coeff_mem
    {L : Type} [Field L] (K₀ : Subfield L) {n : ℕ} (g : Fin n → PowerSeries L)
    (hg : ∀ (i : Fin n) (m : ℕ), (g i).coeff m ∈ K₀)
    (c : Fin n → L) (h : ∀ m : ℕ, (∑ i, c i • g i).coeff m ∈ K₀) :
    ∃ c' : Fin n → L, (∀ i, c' i ∈ K₀) ∧ ∑ i, c' i • g i = ∑ i, c i • g i := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem.solution
