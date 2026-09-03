import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_self_of_map_eq_one_of_isTorsionPoint

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_eq_self_of_map_eq_one_of_isTorsionPoint
    {A : Type u} [CommRing A] (𝒢 : GroupLaws A)
    {T : Type u} [CommRing T] [Algebra A T]
    (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ) (n : ℕ)
    (hP : (𝒢 T x.curve hΔ).IsTorsionPoint (𝟙 _) n x.P) (hQ : (𝒢 T x.curve hΔ).IsTorsionPoint (𝟙 _) n x.Q)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.map (Int.castRingHom (ZMod n)) = 1) :
    ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x hΔ = x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_self_of_map_eq_one_of_isTorsionPoint.solution
