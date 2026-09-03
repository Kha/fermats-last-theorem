import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_residue_norm_quotient_mk_eq_residue_constantCoeff_pow_finrank

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.residue_norm_quotient_mk_eq_residue_constantCoeff_pow_finrank
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (Q : Ideal (UVCrossingModel W (π ^ E)))
    [Module.Free W (UVCrossingModel W (π ^ E) ⧸ Q)] [Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Q)]
    (G : MvPowerSeries (Fin 2) W) :
    residue W (Algebra.norm W (Ideal.Quotient.mk Q (mk (π ^ E) G))) =
      residue W (MvPowerSeries.constantCoeff G) ^ Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_residue_norm_quotient_mk_eq_residue_constantCoeff_pow_finrank.solution
