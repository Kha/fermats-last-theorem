import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_GradedModule_d_sq

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.d_sq {R : Type u} [CommRing R] {n : ℕ} (D : ProjSpaceCech.GradedModule R n) (i : ℕ) :
    ProjSpaceCech.GradedModule.d D (i + 1) ∘ₗ ProjSpaceCech.GradedModule.d D i = 0 := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_d_sq.solution
