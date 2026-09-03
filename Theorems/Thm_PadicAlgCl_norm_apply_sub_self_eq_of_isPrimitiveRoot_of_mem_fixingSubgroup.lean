import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import P2M.Util
import P2M.Sol.S_PadicAlgCl_norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup

set_option autoImplicit false

theorem PadicAlgCl.norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup
    (p : ℕ) [Fact p.Prime] {n k : ℕ} (hkn : k < n) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : σ ∈ (PadicAlgCl.cyclotomicTower p k).fixingSubgroup)
    (hσ' : σ ∉ (PadicAlgCl.cyclotomicTower p (k + 1)).fixingSubgroup) :
    ‖ζ - 1‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p ^ n).totient : ℝ)) ∧
      ‖σ ζ - ζ‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p ^ (n - k)).totient : ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup.solution
