import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import P2M.Util
namespace P2MW.S_TwoChartCech_Cover_LaurentChart_residue_r0

universe u v

theorem solution {R : Type u} [CommRing R] {𝒰 : TwoChartCech.Cover.{u, v} R}
    (Λ : 𝒰.LaurentChart) (h : Λ.IsRegular 𝒰.ρ0) (ω : Ω[𝒰.A0⁄R]) : Λ.residue (𝒰.kaehler.r0 ω) = 0 := by
  have key := KaehlerDifferential.addMonoidHom_ext_smul_D
    (f := Λ.residue.toAddMonoidHom.comp 𝒰.kaehler.r0.toAddMonoidHom) (g := 0) (fun a s => by
      change Λ.residue (𝒰.kaehler.r0 (a • KaehlerDifferential.D R 𝒰.A0 s)) = 0
      rw [TwoChartCech.Cover.kaehler_r0_smul_D, TwoChartCech.Cover.LaurentChart.residue_smul_D]
      obtain ⟨p, hp⟩ := h a
      obtain ⟨q, hq⟩ := h s
      rw [← hp, ← hq]
      exact LaurentSeries.residue_ofPowerSeries_mul_derivative_ofPowerSeries R p q)
  exact DFunLike.congr_fun key ω
