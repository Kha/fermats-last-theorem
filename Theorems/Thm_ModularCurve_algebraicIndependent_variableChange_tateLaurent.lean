import Mathlib
import Definitions.Def_ModularCurve_TateFormal
import P2M.Util
import P2M.Sol.S_ModularCurve_algebraicIndependent_variableChange_tateLaurent
attribute [-instance] WeierstrassCurve.Generic.isElliptic_curve
attribute [-simp] WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃

universe u

theorem ModularCurve.algebraicIndependent_variableChange_tateLaurent (κ : Type u) [Field κ]
    (Ω : Type u) [Field Ω] [Algebra κ Ω] [Algebra (LaurentSeries κ) Ω]
    [IsScalarTower κ (LaurentSeries κ) Ω] (C : WeierstrassCurve.VariableChange Ω)
    (hC : AlgebraicIndependent (LaurentSeries κ) ![(C.u : Ω), C.r, C.s, C.t]) :
    AlgebraicIndependent κ
      ![(C • (ModularCurve.tateLaurent κ).map (algebraMap (LaurentSeries κ) Ω)).a₁,
        (C • (ModularCurve.tateLaurent κ).map (algebraMap (LaurentSeries κ) Ω)).a₂,
        (C • (ModularCurve.tateLaurent κ).map (algebraMap (LaurentSeries κ) Ω)).a₃,
        (C • (ModularCurve.tateLaurent κ).map (algebraMap (LaurentSeries κ) Ω)).a₄,
        (C • (ModularCurve.tateLaurent κ).map (algebraMap (LaurentSeries κ) Ω)).a₆] := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_algebraicIndependent_variableChange_tateLaurent.solution
