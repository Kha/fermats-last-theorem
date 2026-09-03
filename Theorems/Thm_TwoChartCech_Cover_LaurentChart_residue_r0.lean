import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import P2M.Util
import P2M.Sol.S_TwoChartCech_Cover_LaurentChart_residue_r0

universe u v

theorem TwoChartCech.Cover.LaurentChart.residue_r0 {R : Type u} [CommRing R] {𝒰 : TwoChartCech.Cover.{u, v} R}
    (Λ : 𝒰.LaurentChart) (h : Λ.IsRegular 𝒰.ρ0) (ω : Ω[𝒰.A0⁄R]) : Λ.residue (𝒰.kaehler.r0 ω) = 0 := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_Cover_LaurentChart_residue_r0.solution
