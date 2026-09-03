import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_GradedModule_Presentation_ker_isFG

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Presentation.ker_isFG {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) : ProjSpaceCech.GradedModule.IsFG σ.ker := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_Presentation_ker_isFG.solution
