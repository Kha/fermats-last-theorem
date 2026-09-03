import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_norm_quotient_span_eq_finprod_norm_quotient_pow_length

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.norm_quotient_span_eq_finprod_norm_quotient_pow_length
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    [Module.Free W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})]
    [Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})]
    (r : UVCrossingModel W (ϖ ^ e)) :
    Algebra.norm W (Ideal.Quotient.mk (Ideal.span {x}) r) =
      ∏ᶠ (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)))
        (_ : Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ x ∈ Q.asIdeal),
        Algebra.norm W (Ideal.Quotient.mk Q.asIdeal r) ^
          (Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_norm_quotient_span_eq_finprod_norm_quotient_pow_length.solution
