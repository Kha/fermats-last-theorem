import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_of_wild_of_normal

set_option autoImplicit false

theorem ValuationSubring.exists_forall_pow_prime_pow_apply_eq_of_wild_of_normal
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} (hp : p.Prime) (P : ValuationSubring L) (hP : P.LiesOverPrime p)
    {σ : L ≃ₐ[K] L} (hwild : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits)
    (F : IntermediateField K L) [FiniteDimensional K F] [Normal K F] :
    ∃ a : ℕ, ∀ x ∈ F, (σ ^ (p ^ a)) x = x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_of_wild_of_normal.solution
