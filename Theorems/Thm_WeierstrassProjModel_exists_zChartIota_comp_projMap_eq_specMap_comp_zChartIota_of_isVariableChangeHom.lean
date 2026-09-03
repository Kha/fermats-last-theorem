import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel HomogeneousLocalization WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom
    {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hvc : IsVariableChangeHom W C φ) :
    ∃ a : ZChartRing W →+* ZChartRing (C • W),
      zChartι (C • W) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ zChartι W ∧
      (∀ b : T, a (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) b)) =
        fromZeroRingHom (projModelGradingCR (C • W)) _ (algebraMap T ((projModelGradingCR (C • W)) 0) b)) ∧
      a (xOverZ W) =
        fromZeroRingHom (projModelGradingCR (C • W)) _ (algebraMap T ((projModelGradingCR (C • W)) 0) ((C.u : T) ^ 2)) *
          xOverZ (C • W) +
        fromZeroRingHom (projModelGradingCR (C • W)) _ (algebraMap T ((projModelGradingCR (C • W)) 0) C.r) ∧
      a (yOverZ W) =
        fromZeroRingHom (projModelGradingCR (C • W)) _ (algebraMap T ((projModelGradingCR (C • W)) 0) ((C.u : T) ^ 3)) *
          yOverZ (C • W) +
        fromZeroRingHom (projModelGradingCR (C • W)) _
            (algebraMap T ((projModelGradingCR (C • W)) 0) ((C.u : T) ^ 2 * C.s)) * xOverZ (C • W) +
        fromZeroRingHom (projModelGradingCR (C • W)) _ (algebraMap T ((projModelGradingCR (C • W)) 0) C.t) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom.solution
