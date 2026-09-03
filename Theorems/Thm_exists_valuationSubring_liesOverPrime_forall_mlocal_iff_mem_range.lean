import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_exists_valuationSubring_liesOverPrime_forall_mlocal_iff_mem_range

set_option autoImplicit false

theorem exists_valuationSubring_liesOverPrime_forall_mlocal_iff_mem_range
    (p : ℕ) [Fact p.Prime] (ι : AlgebraicClosure ℚ →+* ℂ)
    (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : ↥(integralClosure ℤ ℂ)) ∈ 𝔪) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p ∧
      ∀ z : ℂ, (∃ x y : ↥(integralClosure ℤ ℂ), y ∉ 𝔪 ∧ (x : ℂ) = y * z) ↔
        ∃ a : AlgebraicClosure ℚ, a ∈ A ∧ ι a = z := by p2m_exact_reverting @_root_.P2MW.S_exists_valuationSubring_liesOverPrime_forall_mlocal_iff_mem_range.solution
