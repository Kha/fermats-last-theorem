import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_exists_inertiaSubgroupIn_rootOfUnity_pow_ne_one

set_option autoImplicit false

local notation "Qbar" => AlgebraicClosure ℚ

theorem exists_inertiaSubgroupIn_rootOfUnity_pow_ne_one
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (A : ValuationSubring Qbar) (hA : A.LiesOverPrime ℓ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∃ n a : ℕ,
      (∀ μ : Qbar, μ ^ ℓ ^ n = 1 → σ μ = μ ^ a) ∧ ¬ a ≡ 1 [MOD ℓ ^ n] := by p2m_exact_reverting @_root_.P2MW.S_exists_inertiaSubgroupIn_rootOfUnity_pow_ne_one.solution
