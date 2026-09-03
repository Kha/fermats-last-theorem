import Mathlib
import Definitions.Def_ModularCurve_UVCrossingInitialForm
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_neg_eq_residue_constantCoeff_and_mem_dominantIndices_of_sub_mul_V_pow_mem
set_option autoImplicit false

universe u

open ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.leadingResidue_nfCoeff_neg_eq_residue_constantCoeff_and_mem_dominantIndices_of_sub_mul_V_pow_mem
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (γ : UVCrossingModel W (ϖ ^ e)) (hγ : IsUnit γ) (n : ℕ)
    (hxγ : x - γ * V (ϖ ^ e) ^ n ∈ Ideal.span {const (ϖ ^ e) ϖ, U (ϖ ^ e)})
    (G : MvPowerSeries (Fin 2) W) (hG : mk (ϖ ^ e) G = γ) :
    leadingResidue ϖ (nfCoeff ab (-(n : ℤ))) = IsLocalRing.residue W (MvPowerSeries.constantCoeff G) ∧
      (-(n : ℤ)) ∈ dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (q * e) ab := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_neg_eq_residue_constantCoeff_and_mem_dominantIndices_of_sub_mul_V_pow_mem.solution
