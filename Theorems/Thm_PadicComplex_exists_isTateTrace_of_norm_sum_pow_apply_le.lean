import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PadicComplex_TateTrace
import P2M.Util
import P2M.Sol.S_PadicComplex_exists_isTateTrace_of_norm_sum_pow_apply_le

set_option autoImplicit false

theorem PadicComplex.exists_isTateTrace_of_norm_sum_pow_apply_le
    (p : ℕ) [Fact p.Prime] (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)
    (hfin : ∀ m, FiniteDimensional ℚ_[p] (Km m))
    (hstab : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km 0).fixingSubgroup →
      ∀ y ∈ Km m, σ y ∈ Km m)
    (hdeg : ∀ m n : ℕ, n = m + 1 → Module.finrank ℚ_[p] (Km n) = p * Module.finrank ℚ_[p] (Km m))
    (hcyc : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
      σ ∉ (Km (m + 1)).fixingSubgroup →
        σ ^ p ∈ (Km (m + 1)).fixingSubgroup ∧ σ ^ p ∉ (Km (m + 2)).fixingSubgroup)
    (c : ℕ → ℝ) (C : ℝ) (hc : ∀ m, 1 ≤ c m) (hC : ∀ n, ∏ m ∈ Finset.range n, c m ≤ C)
    (htr : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
      σ ∉ (Km (m + 1)).fixingSubgroup → ∀ y ∈ Km (m + 1),
        ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤ ‖(p : ℚ_[p])‖ * c m * ‖y‖) :
    ∃ d : ℝ, 0 < d ∧ ∀ m, ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p Km m d R := by p2m_exact_reverting @_root_.P2MW.S_PadicComplex_exists_isTateTrace_of_norm_sum_pow_apply_le.solution
