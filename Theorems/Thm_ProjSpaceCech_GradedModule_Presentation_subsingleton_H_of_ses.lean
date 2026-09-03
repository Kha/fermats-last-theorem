import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_GradedModule_Presentation_subsingleton_H_of_ses

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Presentation.subsingleton_H_of_ses {R : Type u} [CommRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) (i : ℕ)
    (hF : Subsingleton (ProjSpaceCech.GradedModule.H σ.F i)) (hK : Subsingleton (ProjSpaceCech.GradedModule.H σ.ker (i + 1))) :
    Subsingleton (ProjSpaceCech.GradedModule.H D i) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_Presentation_subsingleton_H_of_ses.solution
