import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_isUnit

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_isUnit
    {X : Scheme.{u}} (U V : X.Opens) (t : Γ(X, U ⊓ V)) (ht : IsUnit t) :
    ∃ (M : X.Modules) (a : Γ(M, U)) (b : Γ(M, V)),
      Scheme.Modules.IsFrameOn a U ∧ Scheme.Modules.IsFrameOn b V ∧
      M.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b =
        t • M.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_isUnit.solution
