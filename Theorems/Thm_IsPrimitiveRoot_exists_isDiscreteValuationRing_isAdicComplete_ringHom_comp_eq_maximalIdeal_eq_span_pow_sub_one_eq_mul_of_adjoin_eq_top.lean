import Mathlib
import P2M.Util
import P2M.Sol.S_IsPrimitiveRoot_exists_isDiscreteValuationRing_isAdicComplete_ringHom_comp_eq_maximalIdeal_eq_span_pow_sub_one_eq_mul_of_adjoin_eq_top

theorem IsPrimitiveRoot.exists_isDiscreteValuationRing_isAdicComplete_ringHom_comp_eq_maximalIdeal_eq_span_pow_sub_one_eq_mul_of_adjoin_eq_top
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q)

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)})
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A₀ A]
    (hinj : Function.Injective (algebraMap A₀ A)) [Module.Finite A₀ A]
    (ζ : A) (hζ : IsPrimitiveRoot ζ q) (hadj : Algebra.adjoin A₀ {ζ} = ⊤)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] (hW₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {(q : W₀)})
    [Algebra A₀ W₀]

    (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] [Algebra W₀ R₀] [IsLocalHom (algebraMap W₀ R₀)]
    (σ₀ : A →+* R₀)
    (hσ₀ : ∀ a₀ : A₀, σ₀ (algebraMap A₀ A a₀) = algebraMap W₀ R₀ (algebraMap A₀ W₀ a₀)) :
    ∃ (W₁ : Type) (_ : CommRing W₁) (_ : IsDomain W₁) (_ : IsDiscreteValuationRing W₁)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁)
      (j₁ : W₀ →+* W₁) (σ : A →+* W₁) (ι₁ : W₁ →+* R₀) (_ : IsLocalHom ι₁),
      ι₁.comp j₁ = algebraMap W₀ R₀ ∧ ι₁.comp σ = σ₀ ∧
      (∀ a₀ : A₀, σ (algebraMap A₀ A a₀) = j₁ (algebraMap A₀ W₀ a₀)) ∧
      IsLocalRing.maximalIdeal W₁ = Ideal.span {σ ϖ} ∧
      ∃ ε₁ : W₁, IsUnit ε₁ ∧ (σ ϖ) ^ (q - 1) = ε₁ * (q : W₁) := by p2m_exact_reverting @_root_.P2MW.S_IsPrimitiveRoot_exists_isDiscreteValuationRing_isAdicComplete_ringHom_comp_eq_maximalIdeal_eq_span_pow_sub_one_eq_mul_of_adjoin_eq_top.solution
