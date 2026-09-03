import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_exists_ringEquiv_conj_linearPart_C_eq_of_ringEquiv_mvPowerSeries_quotient_of_forall_sub_mem_maximalIdeal

set_option autoImplicit false

p2m_open "IsLocalRing~ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span"

theorem DrinfeldCurve.LocalChart.exists_ringEquiv_conj_linearPart_C_eq_of_ringEquiv_mvPowerSeries_quotient_of_forall_sub_mem_maximalIdeal
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : maximalIdeal W = Ideal.span {ϖ})
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (R : Type) [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]
    (e : R ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C ϖ * v - f * u})
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (hx₀ : e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0)) (hx₁ : e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1))

    (θ₀ : R ≃+* R) (hres : ∀ r : R, θ₀ r - r ∈ maximalIdeal R)
    (hfix : θ₀ (e.symm (Ideal.Quotient.mk _ (MvPowerSeries.C ϖ))) = e.symm (Ideal.Quotient.mk _ (MvPowerSeries.C ϖ)))
    (c : R) (g : Matrix (Fin 2) (Fin 2) ℤ)
    (hlin₀ : θ₀ x₀ - c * (((g 0 0 : ℤ) : R) * x₀ + ((g 1 0 : ℤ) : R) * x₁) ∈ (maximalIdeal R) ^ 2)
    (hlin₁ : θ₀ x₁ - c * (((g 0 1 : ℤ) : R) * x₀ + ((g 1 1 : ℤ) : R) * x₁) ∈ (maximalIdeal R) ^ 2)

    (hc : c ^ (q + 1) - 1 ∈ maximalIdeal R)
    (P P' P'' : Prop) (hP : P → c - 1 ∈ maximalIdeal R) (hP' : P' → P'' → c - 1 ∉ maximalIdeal R) :
    let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C ϖ * v - f * u})
    let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ϖ * v - f * u})
    ∃ (θ : S ≃+* S) (c' : W) (M : Matrix (Fin 2) (Fin 2) W),

      (∀ r : R, θ (e r) = e (θ₀ r)) ∧

      (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

      (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
          mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
        (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
      (c' ^ (q + 1) - 1 ∈ maximalIdeal W) ∧
      (∀ ii jj : Fin 2, M ii jj - c' * ((g ii jj : ℤ) : W) ∈ maximalIdeal W) ∧
      (P → c' - 1 ∈ maximalIdeal W) ∧
      (P' → P'' → c' - 1 ∉ maximalIdeal W) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_exists_ringEquiv_conj_linearPart_C_eq_of_ringEquiv_mvPowerSeries_quotient_of_forall_sub_mem_maximalIdeal.solution
