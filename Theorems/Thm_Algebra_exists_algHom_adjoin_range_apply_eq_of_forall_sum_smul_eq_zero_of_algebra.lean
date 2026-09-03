import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_sum_smul_eq_zero_of_algebra

set_option autoImplicit false

theorem Algebra.exists_algHom_adjoin_range_apply_eq_of_forall_sum_smul_eq_zero_of_algebra
    {K : Type*} [Field K] {F : Type*} [CommRing F] [Algebra K F]
    (L : Type*) [CommRing L] [Algebra K L]
    {ι : Type*} (t : ι → F) (a : ι → L)
    (hone : ∃ i₀, t i₀ = 1 ∧ a i₀ = 1)
    (hmul : ∀ i j, ∃ k, t k = t i * t j ∧ a k = a i * a j)
    (hcons : ∀ (n : ℕ) (idx : Fin n → ι) (c : Fin n → K),
      ∑ l, c l • t (idx l) = 0 → ∑ l, c l • a (idx l) = 0) :
    ∃ χ : ↥(Algebra.adjoin K (Set.range t)) →ₐ[K] L,
      ∀ i, χ ⟨t i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ = a i := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_sum_smul_eq_zero_of_algebra.solution
