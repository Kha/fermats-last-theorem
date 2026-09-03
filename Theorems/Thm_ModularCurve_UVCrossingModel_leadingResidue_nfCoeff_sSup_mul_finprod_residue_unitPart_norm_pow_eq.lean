import Mathlib
import Definitions.Def_ModularCurve_UVCrossingInitialForm
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) :
    leadingResidue ϖ (nfCoeff ab (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab))) *
        ∏ᶠ (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)))
          (_ : Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ x ∈ Q.asIdeal),
          residue W (unitPart ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))))) ^
            (Module.length (Localization.AtPrime Q.asIdeal)
              (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat =
      (-1) ^ (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) -
          sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)).toNat *
        leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.solution
