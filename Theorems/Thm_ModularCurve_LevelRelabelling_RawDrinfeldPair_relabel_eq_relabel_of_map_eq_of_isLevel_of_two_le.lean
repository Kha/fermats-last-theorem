import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

p2m_open "AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal~isDrinfeldBasis_iff_isDrinfeldBasisOver_id"

theorem ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (q : ℕ) (hq : 2 ≤ q)
    (T : Type) [CommRing T] [Algebra A T]
    (W : WeierstrassCurve.Projective T) (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ)
    (hx : RawDrinfeldPair.IsLevel 𝒢 q W x)
    (g g' : Matrix (Fin 2) (Fin 2) ℤ) (hgg' : g.map (Int.castRingHom (ZMod q)) = g'.map (Int.castRingHom (ZMod q))) :
    ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x hΔ =
      ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g' x hΔ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le.solution
