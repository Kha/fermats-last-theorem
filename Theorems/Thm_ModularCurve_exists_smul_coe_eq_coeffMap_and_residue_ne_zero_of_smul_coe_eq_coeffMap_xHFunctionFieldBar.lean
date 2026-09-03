import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (g : ↥(ModularCurve.xHFunctionFieldBar M H)) (hg : g ≠ 0)
    (c₀ : AlgebraicClosure ℚ) (hc₀ : c₀ ≠ 0) (y₀ : LaurentSeries ↥Pl)
    (h₀ : ((c₀ • g : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y₀) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ ∃ y : LaurentSeries ↥Pl,
      ((c • g : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar.solution
