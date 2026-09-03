import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_nonempty_ajFamily_fibre_iso

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.nonempty_ajFamily_fibre_iso
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a]
    (ε t : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t)).obj (ajFamily (a := a) ε) ≅
      pointSubBasepointModule (a := a) t ε) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_nonempty_ajFamily_fibre_iso.solution
