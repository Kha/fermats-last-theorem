import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isUnit_smul_eq

set_option autoImplicit false

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isUnit_smul_eq
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {s s' : Γ(M, U)} {V : X.Opens}
    (hs : Scheme.Modules.IsFrameOn s V) (hs' : Scheme.Modules.IsFrameOn s' V)
    {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) :
    ∃ u : Γ(X, W), IsUnit u ∧
      u • M.presheaf.map (homOfLE hWU).op s = M.presheaf.map (homOfLE hWU).op s' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isUnit_smul_eq.solution
