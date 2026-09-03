import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup_monoidalV2

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.of_iSup_monoidalV2
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {ι : Type v} {s : Γ(M, U)}
    (V : ι → X.Opens) (h : ∀ i, AlgebraicGeometry.Scheme.Modules.IsFrameOn s (V i)) :
    AlgebraicGeometry.Scheme.Modules.IsFrameOn s (⨆ i, V i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup_monoidalV2.solution
