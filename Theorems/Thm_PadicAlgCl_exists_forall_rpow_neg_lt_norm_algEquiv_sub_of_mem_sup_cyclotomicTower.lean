import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import P2M.Util
import P2M.Sol.S_PadicAlgCl_exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower

set_option autoImplicit false

theorem PadicAlgCl.exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower
    (p : ℕ) [Fact p.Prime] (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M]
    [Normal ℚ_[p] M] (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ a : PadicAlgCl p,
      a ∈ M ⊔ PadicAlgCl.cyclotomicTower p n → ‖a‖ ≤ 1 →
      PadicAlgCl.cyclotomicTower p n ≤ IntermediateField.adjoin ℚ_[p] {a} →
      (∀ c ∈ IntermediateField.adjoin ℚ_[p] {a}, ‖c‖ ≤ 1 →
        ∃ P : Polynomial ℚ_[p], (∀ i, ‖P.coeff i‖ ≤ 1) ∧ Polynomial.aeval a P = c) →
      ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        σ ∈ (PadicAlgCl.cyclotomicTower p n).fixingSubgroup → σ a ≠ a →
        (p : ℝ) ^ (-ε) < ‖σ a - a‖ := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower.solution
