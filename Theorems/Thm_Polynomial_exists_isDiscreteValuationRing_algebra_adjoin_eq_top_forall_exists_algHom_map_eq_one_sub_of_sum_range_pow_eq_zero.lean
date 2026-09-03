import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero

set_option autoImplicit false

open IsLocalRing Polynomial

theorem Polynomial.exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q)
    (Z₀ : Type) [CommRing Z₀] [IsDomain Z₀] [IsDiscreteValuationRing Z₀]
    (hZ₀ : maximalIdeal Z₀ = Ideal.span {(q : Z₀)}) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra Z₀ V)
      (_ : Module.Finite Z₀ V) (_ : Module.Free Z₀ V)
      (_ : Finite (ResidueField Z₀) → Finite (ResidueField V))
      (ϖ : V) (_ : maximalIdeal V = Ideal.span {ϖ}) (_ : Algebra.adjoin Z₀ {ϖ} = ⊤)
      (ε : V) (_ : IsUnit ε) (_ : ϖ ^ (q - 1) = ε * (q : V))
      (_ : ∑ i ∈ Finset.range q, (1 - ϖ) ^ i = 0),
      ∀ (R : Type) [CommRing R] [Algebra Z₀ R] (ζ : R), ∑ i ∈ Finset.range q, ζ ^ i = 0 →
        ∃ ι : V →ₐ[Z₀] R, ι ϖ = 1 - ζ := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero.solution
