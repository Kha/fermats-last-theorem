import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_exists_semilinear_linearPart_transport_of_forall_specialLinearGroup_of_dense_of_prime

set_option autoImplicit false

open scoped MatrixGroups

theorem DrinfeldCurve.LocalChart.exists_semilinear_linearPart_transport_of_forall_specialLinearGroup_of_dense_of_prime
    (q : ℕ) [Fact q.Prime]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (hqA : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A)

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] (σ₀ : A →+* W₀)
    (hσϖ₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {σ₀ ϖ})
    (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀) (hu₀ : IsUnit u₀) (hv₀ : IsUnit v₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ (q + 2))
    [IsLocalRing (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀})]

    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W] (σ : A →+* W)
    (hσϖ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    [IsLocalRing (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u})]
    [IsHausdorff (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u})) (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u})]

    (β : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀}) ≃+* (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u}))
    (D : Type) [CommRing D] (ψ₀ : D →+* (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀})) (ψ : D →+* (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u}))

    (τ : D →+* D) (σA : A ≃+* A) (x : A) (N : Matrix (Fin 2) (Fin 2) ℕ)
    (θ₀ : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀}) ≃+* (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀})) (σW₀ : W₀ ≃+* W₀) (ct₀ : W₀) (M₀ : Matrix (Fin 2) (Fin 2) W₀) :
    let S₀ := (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀})
    let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u})
    let mk₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀})
    let mk : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ t) * v - f * u})
    let J₀ : Ideal S₀ := Ideal.span {mk₀ (MvPowerSeries.X 0), mk₀ (MvPowerSeries.X 1)}
    let J : Ideal S := Ideal.span {mk (MvPowerSeries.X 0), mk (MvPowerSeries.X 1)}

    (∀ a : A, β (mk₀ (MvPowerSeries.C (σ₀ a))) = mk (MvPowerSeries.C (σ a))) →

    (∀ w : W₀, ∃ a : A, mk₀ (MvPowerSeries.C (w - σ₀ a)) ∈ IsLocalRing.maximalIdeal S₀) →
    (∀ w : W, ∃ a : A, mk (MvPowerSeries.C (w - σ a)) ∈ IsLocalRing.maximalIdeal S) →

    (∀ d : D, β (ψ₀ d) = ψ d) →
    (∀ (s : S₀) (n : ℕ), ∃ d : D, s - ψ₀ d ∈ (IsLocalRing.maximalIdeal S₀) ^ n) →

    (∀ g : SL(2, ZMod q), ∃ (G : Matrix (Fin 2) (Fin 2) ℤ) (τg : D →+* D)
        (θ₀g : S₀ ≃+* S₀) (θg : S ≃+* S) (M₀g : Matrix (Fin 2) (Fin 2) W₀) (Mg : Matrix (Fin 2) (Fin 2) W),
      (∀ ii jj : Fin 2, ((G ii jj : ℤ) : ZMod q) = ((g : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj) ∧
      (∀ d : D, θ₀g (ψ₀ d) = ψ₀ (τg d)) ∧ (∀ d : D, θg (ψ d) = ψ (τg d)) ∧
      (∀ w : W₀, θ₀g (mk₀ (MvPowerSeries.C w)) = mk₀ (MvPowerSeries.C w)) ∧
      (∀ w : W, θg (mk (MvPowerSeries.C w)) = mk (MvPowerSeries.C w)) ∧
      (∀ jj : Fin 2, θ₀g (mk₀ (MvPowerSeries.X jj)) -
          mk₀ (∑ ii : Fin 2, MvPowerSeries.C (M₀g ii jj) * MvPowerSeries.X ii) ∈ J₀ ^ 2) ∧
      (∀ jj : Fin 2, θg (mk (MvPowerSeries.X jj)) -
          mk (∑ ii : Fin 2, MvPowerSeries.C (Mg ii jj) * MvPowerSeries.X ii) ∈ J ^ 2) ∧
      (∀ ii jj : Fin 2, M₀g ii jj - ((G ii jj : ℤ) : W₀) ∈ IsLocalRing.maximalIdeal W₀) ∧
      (∀ ii jj : Fin 2, Mg ii jj - ((G ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W)) →

    (∀ d : D, θ₀ (ψ₀ d) = ψ₀ (τ d)) →
    (∀ a : A, σW₀ (σ₀ a) = σ₀ (σA a)) →
    (∀ w : W₀, σW₀ w - w ∈ IsLocalRing.maximalIdeal W₀) →
    (∀ w : W₀, θ₀ (mk₀ (MvPowerSeries.C w)) = mk₀ (MvPowerSeries.C (σW₀ w))) →
    (∀ jj : Fin 2, θ₀ (mk₀ (MvPowerSeries.X jj)) -
        mk₀ (∑ ii : Fin 2, MvPowerSeries.C (M₀ ii jj) * MvPowerSeries.X ii) ∈ J₀ ^ 2) →
    (ct₀ - σ₀ x ∈ IsLocalRing.maximalIdeal W₀) →
    (∀ ii jj : Fin 2, M₀ ii jj - ct₀ * ((N ii jj : ℕ) : W₀) ∈ IsLocalRing.maximalIdeal W₀) →

    ∃ (θ : S ≃+* S) (σW : W ≃+* W) (ct : W) (M : Matrix (Fin 2) (Fin 2) W),
      (∀ d : D, θ (ψ d) = ψ (τ d)) ∧
      (∀ a : A, σW (σ a) = σ (σA a)) ∧
      (∀ w : W, σW w - w ∈ IsLocalRing.maximalIdeal W) ∧
      (∀ w : W, θ (mk (MvPowerSeries.C w)) = mk (MvPowerSeries.C (σW w))) ∧
      (∀ jj : Fin 2, θ (mk (MvPowerSeries.X jj)) -
          mk (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈ J ^ 2) ∧
      (ct - σ x ∈ IsLocalRing.maximalIdeal W) ∧
      (∀ ii jj : Fin 2, M ii jj - ct * ((N ii jj : ℕ) : W) ∈ IsLocalRing.maximalIdeal W) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_exists_semilinear_linearPart_transport_of_forall_specialLinearGroup_of_dense_of_prime.solution
