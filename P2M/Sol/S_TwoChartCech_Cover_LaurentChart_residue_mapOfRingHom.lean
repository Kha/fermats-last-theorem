import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import P2M.Util
namespace P2MW.S_TwoChartCech_Cover_LaurentChart_residue_mapOfRingHom

universe u v

theorem solution {R : Type u} {S : Type u} [CommRing R] [CommRing S]
    {𝒰 : TwoChartCech.Cover.{u, v} R} {𝒲 : TwoChartCech.Cover.{u, v} S}
    (τ : R →+* S) (φ : 𝒰.A01 →+* 𝒲.A01)
    (h : φ.comp (algebraMap R 𝒰.A01) = (algebraMap S 𝒲.A01).comp τ)
    (Λ : 𝒰.LaurentChart) (Λ' : 𝒲.LaurentChart) (hΛ : ∀ y : 𝒰.A01, Λ'.expand (φ y) = (Λ.expand y).map τ)
    (η : Ω[𝒰.A01⁄R]) :
    Λ'.residue (KaehlerDifferential.mapOfRingHom τ φ h η) = τ (Λ.residue η) := by
  have key := KaehlerDifferential.addMonoidHom_ext_smul_D
    (f := Λ'.residue.toAddMonoidHom.comp (KaehlerDifferential.mapOfRingHom τ φ h).toAddMonoidHom)
    (g := τ.toAddMonoidHom.comp Λ.residue.toAddMonoidHom) (fun a s => by
      change Λ'.residue (KaehlerDifferential.mapOfRingHom τ φ h (a • KaehlerDifferential.D R 𝒰.A01 s)) =
        τ (Λ.residue (a • KaehlerDifferential.D R 𝒰.A01 s))
      rw [KaehlerDifferential.mapOfRingHom_smul_D, TwoChartCech.Cover.LaurentChart.residue_smul_D,
        TwoChartCech.Cover.LaurentChart.residue_smul_D, hΛ, hΛ, ← LaurentSeries.map_derivative, ← HahnSeries.map_coeff]
      congr 1
      exact (HahnSeries.map_mul τ.toNonUnitalRingHom).symm)
  exact DFunLike.congr_fun key η
