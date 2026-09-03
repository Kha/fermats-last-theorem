import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import P2M.Util
import P2M.Sol.S_PadicAlgCl_norm_apply_sub_le_norm_apply_sub_of_mem_cyclotomicTower

set_option autoImplicit false

theorem PadicAlgCl.norm_apply_sub_le_norm_apply_sub_of_mem_cyclotomicTower
    (p : ℕ) [Fact p.Prime] {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {y : PadicAlgCl p}
    (hy : y ∈ PadicAlgCl.cyclotomicTower p n) (hy1 : ‖y‖ ≤ 1) :
    ‖σ y - y‖ ≤ ‖σ ζ - ζ‖ := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_norm_apply_sub_le_norm_apply_sub_of_mem_cyclotomicTower.solution
