import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.pullback_of_isPullback
    {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R')
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of R)} {f' : X' ⟶ Spec (.of R')} (g : X' ⟶ X)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {M : X.Modules} (hM : Scheme.Modules.ClosedImmersionBySections M f) :
    Scheme.Modules.ClosedImmersionBySections ((Scheme.Modules.pullback g).obj M) f' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_of_isPullback.solution
