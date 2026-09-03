import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_isUnit_of_isFrameOn_smul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.isUnit_of_isFrameOn_smul
    {X : Scheme.{u}} {M : X.Modules} {U V W : X.Opens} (s : Γ(M, U))
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (hWU : W ≤ U) (hWV : W ≤ V) (g : Γ(X, W))
    (hg : AlgebraicGeometry.Scheme.Modules.IsFrameOn (g • M.presheaf.map (homOfLE hWU).op s) W) :
    IsUnit g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_isUnit_of_isFrameOn_smul.solution
