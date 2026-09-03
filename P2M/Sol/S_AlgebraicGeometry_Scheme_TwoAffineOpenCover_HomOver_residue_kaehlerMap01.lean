import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_residue_kaehlerMap01

universe u v

theorem residue_mapOfRingHom_aux {R : Type u} {S : Type u} [CommRing R] [CommRing S]
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

theorem solution {R : Type u} {S : Type u} [CommRing R] [CommRing S] {τ : R →+* S} {X : AlgebraicGeometry.Scheme.{u}}
    {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ AlgebraicGeometry.Spec (.of R)} {Y : AlgebraicGeometry.Scheme.{u}}
    {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ AlgebraicGeometry.Spec (.of S)}
    (f : AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver τ 𝒱 c 𝒲 c')
    (Λ : (𝒱.cover c).LaurentChart) (Λ' : (𝒲.cover c').LaurentChart)
    (hΛ : ∀ y : (𝒱.cover c).A01, Λ'.expand (f.map01 y) = (Λ.expand y).map τ) (η : Ω[(𝒱.cover c).A01⁄R]) :
    Λ'.residue (f.kaehlerMap01 η) = τ (Λ.residue η) := by
  exact residue_mapOfRingHom_aux τ f.ringHom01 f.ringHom01_comp_algebraMap Λ Λ' hΛ η
