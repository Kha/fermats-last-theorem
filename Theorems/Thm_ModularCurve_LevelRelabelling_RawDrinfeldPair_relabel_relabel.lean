import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_relabel

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_relabel
    {A : Type u} [CommRing A] (𝒢 : GroupLaws A)
    {T : Type u} [CommRing T] [Algebra A T]
    (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ)
    (hcomm : ∀ P Q : Section x.curve, (𝒢 T x.curve hΔ).mul _ P Q = (𝒢 T x.curve hΔ).mul _ Q P)
    (g g' : Matrix (Fin 2) (Fin 2) ℤ) :
    ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g'
        (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x hΔ) hΔ =
      ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 (g * g') x hΔ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_relabel.solution
