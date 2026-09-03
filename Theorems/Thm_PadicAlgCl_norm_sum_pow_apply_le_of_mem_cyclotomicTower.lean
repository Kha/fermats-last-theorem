import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import P2M.Util
import P2M.Sol.S_PadicAlgCl_norm_sum_pow_apply_le_of_mem_cyclotomicTower

set_option autoImplicit false

theorem PadicAlgCl.norm_sum_pow_apply_le_of_mem_cyclotomicTower (p : ℕ) [Fact p.Prime]
    (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : σ ∈ (PadicAlgCl.cyclotomicTower p (m + 2)).fixingSubgroup)
    (hσ' : σ ∉ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup)
    (y : PadicAlgCl p) (hy : y ∈ PadicAlgCl.cyclotomicTower p (m + 3)) :
    ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤
      ‖(p : ℚ_[p])‖ * (p : ℝ) ^ (1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1))) * ‖y‖ := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_norm_sum_pow_apply_le_of_mem_cyclotomicTower.solution
