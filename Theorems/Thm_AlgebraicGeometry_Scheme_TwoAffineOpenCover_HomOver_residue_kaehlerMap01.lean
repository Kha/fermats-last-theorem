import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_residue_kaehlerMap01

universe u v

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.residue_kaehlerMap01 {R : Type u} {S : Type u} [CommRing R] [CommRing S] {τ : R →+* S} {X : AlgebraicGeometry.Scheme.{u}}
    {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ AlgebraicGeometry.Spec (.of R)} {Y : AlgebraicGeometry.Scheme.{u}}
    {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ AlgebraicGeometry.Spec (.of S)}
    (f : AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver τ 𝒱 c 𝒲 c')
    (Λ : (𝒱.cover c).LaurentChart) (Λ' : (𝒲.cover c').LaurentChart)
    (hΛ : ∀ y : (𝒱.cover c).A01, Λ'.expand (f.map01 y) = (Λ.expand y).map τ) (η : Ω[(𝒱.cover c).A01⁄R]) :
    Λ'.residue (f.kaehlerMap01 η) = τ (Λ.residue η) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_residue_kaehlerMap01.solution
