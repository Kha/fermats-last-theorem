import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Theorems.Thm_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD
import Theorems.Thm_ProjSpaceCech_Twist_finite_cohomology
import P2M.Util
namespace P2MW.S_ProjSpaceCech_GradedModule_finite_cohomology_FD

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function MvPolynomial

theorem solution (R : Type u) [CommRing R] (n : ℕ) (d₀ : ℤ) (i : ℕ) :
    Module.Finite R (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.FD R n d₀) i) :=
  by
  obtain ⟨e⟩ := ProjSpaceCech.GradedModule.nonempty_HEquiv_FD R n d₀ i
  haveI := ProjSpaceCech.Twist.finite_cohomology R n d₀ i
  exact Module.Finite.equiv e

end
