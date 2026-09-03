import Mathlib.Data.ZMod.Basic
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (a : (ZMod p)ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ (a : ZMod p).val := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow.solution
