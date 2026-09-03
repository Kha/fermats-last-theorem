import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import P2M.Util
import P2M.Sol.S_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup

set_option autoImplicit false

theorem PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup (p : ℕ) [Fact p.Prime] :
    (∀ n : ℕ, 0 < n →
      Module.finrank ℚ_[p] (PadicAlgCl.cyclotomicTower p n) = (p - 1) * p ^ (n - 1)) ∧
    (∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      σ ∈ (PadicAlgCl.cyclotomicTower p (m + 2)).fixingSubgroup →
      σ ∉ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup →
        σ ^ p ∈ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup ∧
          σ ^ p ∉ (PadicAlgCl.cyclotomicTower p (m + 4)).fixingSubgroup) := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup.solution
