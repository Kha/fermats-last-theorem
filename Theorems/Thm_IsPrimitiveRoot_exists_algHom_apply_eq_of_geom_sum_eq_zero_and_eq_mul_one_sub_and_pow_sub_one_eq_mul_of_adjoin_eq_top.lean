import Mathlib
import P2M.Util
import P2M.Sol.S_IsPrimitiveRoot_exists_algHom_apply_eq_of_geom_sum_eq_zero_and_eq_mul_one_sub_and_pow_sub_one_eq_mul_of_adjoin_eq_top

theorem IsPrimitiveRoot.exists_algHom_apply_eq_of_geom_sum_eq_zero_and_eq_mul_one_sub_and_pow_sub_one_eq_mul_of_adjoin_eq_top
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)})
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A₀ A]
    (hinj : Function.Injective (algebraMap A₀ A)) [Module.Finite A₀ A]
    (ζ : A) (hζ : IsPrimitiveRoot ζ q) (hadj : Algebra.adjoin A₀ {ζ} = ⊤)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    (∀ (S : Type) [CommRing S] [Algebra A₀ S] (z : S), (∑ i ∈ Finset.range q, z ^ i) = 0 →
        ∃ f : A →ₐ[A₀] S, f ζ = z) ∧
    (∃ u : A, IsUnit u ∧ ϖ = u * (1 - ζ)) ∧
    (∃ ε : A, IsUnit ε ∧ ϖ ^ (q - 1) = ε * (q : A)) := by p2m_exact_reverting @_root_.P2MW.S_IsPrimitiveRoot_exists_algHom_apply_eq_of_geom_sum_eq_zero_and_eq_mul_one_sub_and_pow_sub_one_eq_mul_of_adjoin_eq_top.solution
