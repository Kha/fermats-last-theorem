import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_exists_sq_ne_one_and_forall_apply_eq_zero_iff_of_card_eq_of_forall_apply_pow_eq

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.exists_sq_ne_one_and_forall_apply_eq_zero_iff_of_card_eq_of_forall_apply_pow_eq
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (m : ((GaloisField q 2)ˣ →* Kˣ) →₀ ℕ)
    (S₀ : Finset ((GaloisField q 2)ˣ →* Kˣ)) (hS₀ : ∀ μ : (GaloisField q 2)ˣ →* Kˣ,
      μ ∈ S₀ ↔ ∀ c : (ZMod q)ˣ, μ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1) (hcard : S₀.card = q + 1)
    (hle : ∀ μ, m μ ≤ 1) (h1 : m 1 = 1) (hsupp : ∀ μ ∈ m.support, μ ∈ S₀)
    (hsum : (m.sum fun _ n => n) = q - 1) (hsym : ∀ μ, m (μ ^ q) = m μ) :
    ∃ θ ∈ S₀, θ ^ 2 ≠ 1 ∧ ∀ μ ∈ S₀, m μ = 0 ↔ (μ = θ ∨ μ = θ⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_exists_sq_ne_one_and_forall_apply_eq_zero_iff_of_card_eq_of_forall_apply_pow_eq.solution
