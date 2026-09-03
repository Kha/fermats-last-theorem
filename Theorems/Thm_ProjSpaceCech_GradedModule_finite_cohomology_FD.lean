import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_GradedModule_finite_cohomology_FD

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.finite_cohomology_FD (R : Type u) [CommRing R] (n : ℕ) (d₀ : ℤ) (i : ℕ) :
    Module.Finite R (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.FD R n d₀) i) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_finite_cohomology_FD.solution
