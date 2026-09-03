import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isStackFor_openCover

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isStackFor_openCover (Y : Scheme.{u}) (𝒰 : Y.OpenCover) :
    ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).IsStackFor
      (Presieve.ofArrows 𝒰.X 𝒰.f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isStackFor_openCover.solution
