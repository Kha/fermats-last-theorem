import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_finsupp_apply_pow_eq_of_forall_character_torus_eq_sum

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.finsupp_apply_pow_eq_of_forall_character_torus_eq_sum
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    [Fintype (GaloisField q 2)ˣ] (ρ : Representation K (GL2 q) V)
    (m : ((GaloisField q 2)ˣ →* Kˣ) →₀ ℕ)
    (htr : ∀ α, ρ.character (torus q α) = m.sum fun μ n => (n : K) * ((μ α : Kˣ) : K)) (μ : (GaloisField q 2)ˣ →* Kˣ) :
    m (μ ^ q) = m μ := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_finsupp_apply_pow_eq_of_forall_character_torus_eq_sum.solution
