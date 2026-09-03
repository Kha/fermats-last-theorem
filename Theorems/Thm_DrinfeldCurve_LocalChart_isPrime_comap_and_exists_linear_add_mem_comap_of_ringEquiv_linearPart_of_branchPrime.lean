import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_isPrime_comap_and_exists_linear_add_mem_comap_of_ringEquiv_linearPart_of_branchPrime

set_option autoImplicit false

open scoped MatrixGroups

theorem DrinfeldCurve.LocalChart.isPrime_comap_and_exists_linear_add_mem_comap_of_ringEquiv_linearPart_of_branchPrime
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : IsLocalRing.maximalIdeal W = Ideal.span {π})
    (hqW : (q : W) ∈ IsLocalRing.maximalIdeal W)
    (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) (hc0 : c ≠ 0)
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))

    (θ : (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u}) ≃+*
      (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u}))
    (hθW : ∀ w : W, θ (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.C w)) =
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.C w))

    (M : Matrix (Fin 2) (Fin 2) W)
    (hθM : ∀ jj : Fin 2, θ (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X jj)) -
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 1)}) ^ 2)

    (c₁ : W) (hc₁ : c₁ ∉ IsLocalRing.maximalIdeal W) (g : SL(2, ℤ))
    (hMg : ∀ ii jj : Fin 2, M ii jj - c₁ * ((g ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W)

    (P : Ideal (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u})) (hP : P.IsPrime)
    (hPX : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 0) ∉ P ∨
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 1) ∉ P)
    (hPπ : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.C π) ∈ P)

    (a b A B : ℤ)
    (hA : (q : ℤ) ∣ A - ((g 0 0 : ℤ) * a + (g 0 1 : ℤ) * b))
    (hB : (q : ℤ) ∣ B - ((g 1 0 : ℤ) * a + (g 1 1 : ℤ) * b))
    (hAB : ∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u})
        (MvPowerSeries.C ((A : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((B : ℤ) : W) * MvPowerSeries.X 1 + h) ∈ P) :
    let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u})
    let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u})
    (P.comap (θ : S →+* S)).IsPrime ∧
    (mkS (MvPowerSeries.X 0) ∉ P.comap (θ : S →+* S) ∨ mkS (MvPowerSeries.X 1) ∉ P.comap (θ : S →+* S)) ∧
    mkS (MvPowerSeries.C π) ∈ P.comap (θ : S →+* S) ∧
    ∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
      mkS (MvPowerSeries.C ((a : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b : ℤ) : W) * MvPowerSeries.X 1 + h) ∈
        P.comap (θ : S →+* S) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_isPrime_comap_and_exists_linear_add_mem_comap_of_ringEquiv_linearPart_of_branchPrime.solution
