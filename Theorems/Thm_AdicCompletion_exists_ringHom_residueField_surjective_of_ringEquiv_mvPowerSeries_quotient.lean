import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_ringHom_residueField_surjective_of_ringEquiv_mvPowerSeries_quotient

set_option autoImplicit false

open IsLocalRing MvPowerSeries

theorem AdicCompletion.exists_ringHom_residueField_surjective_of_ringEquiv_mvPowerSeries_quotient
    (B₀ : Type) [CommRing B₀] (𝔪₀ : Ideal B₀) [𝔪₀.IsMaximal]
    (W₀ : Type) [CommRing W₀] [IsLocalRing W₀]
    (g₀ : MvPowerSeries (Fin 2) W₀) (hg₀ : MvPowerSeries.constantCoeff g₀ ∈ maximalIdeal W₀)
    (e₀ : AdicCompletion 𝔪₀ B₀ ≃+* MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}) :
    ∃ ρ : B₀ →+* ResidueField W₀,
      Function.Surjective ρ ∧ RingHom.ker ρ = 𝔪₀ ∧
      ∀ (b : B₀) (w : W₀),
        e₀ (algebraMap B₀ (AdicCompletion 𝔪₀ B₀) b) - Ideal.Quotient.mk (Ideal.span {g₀}) (C w) ∈
          (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1} ⊔
            (maximalIdeal W₀).map (C : W₀ →+* MvPowerSeries (Fin 2) W₀)).map
            (Ideal.Quotient.mk (Ideal.span {g₀})) →
        ρ b = residue W₀ w := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_ringHom_residueField_surjective_of_ringEquiv_mvPowerSeries_quotient.solution
