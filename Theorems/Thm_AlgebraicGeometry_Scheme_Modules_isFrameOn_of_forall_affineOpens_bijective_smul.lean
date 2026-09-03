import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isFrameOn_of_forall_affineOpens_bijective_smul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.isFrameOn_of_forall_affineOpens_bijective_smul
    {X : Scheme.{u}} (N : X.Modules) (U : X.Opens) (s : Γ(N, U))
    (h : ∀ (W : X.affineOpens) (hW : W.1 ≤ U),
      Function.Bijective (fun a : Γ(X, W.1) => a • (N.presheaf.map (homOfLE hW).op s : Γ(N, W.1)))) :
    Scheme.Modules.IsFrameOn s U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isFrameOn_of_forall_affineOpens_bijective_smul.solution
