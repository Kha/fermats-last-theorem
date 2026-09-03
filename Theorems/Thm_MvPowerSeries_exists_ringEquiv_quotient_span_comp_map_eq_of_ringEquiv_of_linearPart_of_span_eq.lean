import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_ringEquiv_quotient_span_comp_map_eq_of_ringEquiv_of_linearPart_of_span_eq

set_option autoImplicit false

open MvPowerSeries

theorem MvPowerSeries.exists_ringEquiv_quotient_span_comp_map_eq_of_ringEquiv_of_linearPart_of_span_eq
    (W₀ W : Type) [CommRing W₀] [IsNoetherianRing W₀] [CommRing W] [IsNoetherianRing W]
    (ψ : W₀ →+* W) (g₀ : MvPowerSeries (Fin 2) W₀) (g : MvPowerSeries (Fin 2) W)
    (hg : Ideal.span {g} = Ideal.span {MvPowerSeries.map ψ g₀})
    (θ₀ : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}) ≃+* (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}))
    (M₀ : Matrix (Fin 2) (Fin 2) W₀)

    (hθ₀C : ∀ w : W₀, θ₀ (Ideal.Quotient.mk (Ideal.span {g₀}) (C w)) = Ideal.Quotient.mk (Ideal.span {g₀}) (C w))

    (hθ₀X : ∀ jj : Fin 2,
      θ₀ (Ideal.Quotient.mk (Ideal.span {g₀}) (X jj)) -
          Ideal.Quotient.mk (Ideal.span {g₀}) (∑ ii : Fin 2, C (M₀ ii jj) * X ii) ∈
        (Ideal.span {Ideal.Quotient.mk (Ideal.span {g₀}) (X 0 : MvPowerSeries (Fin 2) W₀),
          Ideal.Quotient.mk (Ideal.span {g₀}) (X 1)}) ^ 2) :
    let S₀ := MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}
    let mkS₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk (Ideal.span {g₀})
    let S := MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}
    let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {g})
    ∃ θ : S ≃+* S,

      (∀ w : W, θ (mkS (C w)) = mkS (C w)) ∧

      (∀ s s' : MvPowerSeries (Fin 2) W₀, θ₀ (mkS₀ s) = mkS₀ s' →
        θ (mkS (MvPowerSeries.map ψ s)) = mkS (MvPowerSeries.map ψ s')) ∧

      (∀ jj : Fin 2,
        θ (mkS (X jj)) - mkS (∑ ii : Fin 2, C (ψ (M₀ ii jj)) * X ii) ∈
          (Ideal.span {mkS (X 0), mkS (X 1)}) ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_ringEquiv_quotient_span_comp_map_eq_of_ringEquiv_of_linearPart_of_span_eq.solution
