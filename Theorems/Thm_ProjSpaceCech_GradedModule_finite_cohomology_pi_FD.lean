import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_GradedModule_finite_cohomology_pi_FD

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.finite_cohomology_pi_FD (R : Type u) [CommRing R] (n : ℕ) {ι : Type} [Fintype ι] (d₀ : ι → ℤ) (i : ℕ) :
    Module.Finite R (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.pi (fun k => ProjSpaceCech.GradedModule.FD R n (d₀ k))) i) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_finite_cohomology_pi_FD.solution
