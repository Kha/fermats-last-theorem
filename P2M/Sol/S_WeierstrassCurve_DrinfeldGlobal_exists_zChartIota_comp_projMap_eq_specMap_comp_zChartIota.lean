import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization WeierstrassCurve.DrinfeldGlobal

theorem solution
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ) :
    ∃ a : ZChartRing W →+* ZChartRing (W.map f),
      zChartι (W.map f) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ zChartι W ∧
      a (xOverZ W) = xOverZ (W.map f) ∧ a (yOverZ W) = yOverZ (W.map f) := by
  obtain ⟨-, hX⟩ := hcoef
  have key : ∀ (s : ProjModelRingCR (W.map f)) (hs : s ∈ projModelGradingCR (W.map f) 1)
      (e : φ (coord W 2) = s),
      ∃ a : ZChartRing W →+* Away (projModelGradingCR (W.map f)) s,
        Proj.awayι (projModelGradingCR (W.map f)) s hs one_pos ≫ Proj.map φ hφ =
          Spec.map (CommRingCat.ofHom a) ≫ zChartι W ∧
        a (xOverZ W) = Away.mk (projModelGradingCR (W.map f)) hs 1 (coord (W.map f) 0)
          (by simpa using coord_mem (W.map f) 0) ∧
        a (yOverZ W) = Away.mk (projModelGradingCR (W.map f)) hs 1 (coord (W.map f) 1)
          (by simpa using coord_mem (W.map f) 1) := by
    intro s hs e
    subst e
    refine ⟨Away.map φ (coord W 2), ?_, ?_, ?_⟩
    · exact Proj.awayι_comp_map φ hφ one_pos (coord W 2) (coord_mem W 2)
    · show Away.map φ (coord W 2) (Away.mk _ (coord_mem W 2) 1 (coord W 0) _) = _
      rw [Away.map_mk]
      apply HomogeneousLocalization.val_injective
      simp only [Away.val_mk]
      congr 1
      · exact hX 0
    · show Away.map φ (coord W 2) (Away.mk _ (coord_mem W 2) 1 (coord W 1) _) = _
      rw [Away.map_mk]
      apply HomogeneousLocalization.val_injective
      simp only [Away.val_mk]
      congr 1
      · exact hX 1
  exact key (coord (W.map f) 2) (coord_mem (W.map f) 2) (hX 2)
