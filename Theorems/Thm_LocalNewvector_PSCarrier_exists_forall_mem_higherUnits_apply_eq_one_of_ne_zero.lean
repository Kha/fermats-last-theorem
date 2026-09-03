import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import P2M.Util
import P2M.Sol.S_LocalNewvector_PSCarrier_exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero

set_option autoImplicit false

theorem LocalNewvector.PSCarrier.exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero
    (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) (F : LocalNewvector.PSCarrier p μ₁ μ₂)
    (hF : F ≠ 0) :
    ∃ c : ℕ, ∀ u ∈ LocalNewvector.higherUnits p c, μ₁ u = 1 ∧ μ₂ u = 1 := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_PSCarrier_exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero.solution
