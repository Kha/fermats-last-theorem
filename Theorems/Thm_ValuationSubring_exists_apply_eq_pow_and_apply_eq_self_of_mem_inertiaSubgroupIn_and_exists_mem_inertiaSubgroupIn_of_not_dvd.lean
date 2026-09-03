import Mathlib.Data.ZMod.Basic
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_apply_eq_pow_and_apply_eq_self_of_mem_inertiaSubgroupIn_and_exists_mem_inertiaSubgroupIn_of_not_dvd

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem ValuationSubring.exists_apply_eq_pow_and_apply_eq_self_of_mem_inertiaSubgroupIn_and_exists_mem_inertiaSubgroupIn_of_not_dvd
    (q : ℕ) (hq : q.Prime) (c N' : ℕ) (hN' : ¬ q ∣ N')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q) :
    (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ x : (ZMod (q ^ c))ˣ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ q ^ c = 1 → σ μ = μ ^ (x : ZMod (q ^ c)).val) ∧
      (∀ μ : AlgebraicClosure ℚ, μ ^ N' = 1 → σ μ = μ)) ∧
    (∀ x : (ZMod (q ^ c))ˣ, ∃ σ ∈ P.inertiaSubgroupIn ℚ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ q ^ c = 1 → σ μ = μ ^ (x : ZMod (q ^ c)).val) ∧
      (∀ μ : AlgebraicClosure ℚ, μ ^ N' = 1 → σ μ = μ)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_apply_eq_pow_and_apply_eq_self_of_mem_inertiaSubgroupIn_and_exists_mem_inertiaSubgroupIn_of_not_dvd.solution
