import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_algEquiv_localization_atPrime_mvPowerSeries_quotient_apply_mk

set_option autoImplicit false

open scoped TensorProduct

theorem MvPolynomial.exists_algEquiv_localization_atPrime_mvPowerSeries_quotient_apply_mk
    (K : Type*) [Field K] {m r : ℕ} (g : Fin r → MvPolynomial (Fin m) K)
    (𝔫 : Ideal (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))) [𝔫.IsMaximal]
    (h𝔫 : ∀ j, Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X j) ∈ 𝔫)
    [Module.Finite K (Localization.AtPrime 𝔫)] :
    ∃ e : Localization.AtPrime 𝔫 ≃ₐ[K]
      (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K))),
      ∀ p : MvPolynomial (Fin m) K,
        e (algebraMap (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) (Localization.AtPrime 𝔫)
            (Ideal.Quotient.mk (Ideal.span (Set.range g)) p)) =
          Ideal.Quotient.mk (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K)))
            (p : MvPowerSeries (Fin m) K) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_algEquiv_localization_atPrime_mvPowerSeries_quotient_apply_mk.solution
