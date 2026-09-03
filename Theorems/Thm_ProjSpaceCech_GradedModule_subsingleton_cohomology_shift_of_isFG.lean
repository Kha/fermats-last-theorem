import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (M : ProjSpaceCech.GradedModule R n) (hM : ProjSpaceCech.GradedModule.IsFG M) :
    ∃ d₀ : ℤ, ∀ d, d₀ ≤ d → ∀ i, 1 ≤ i → Subsingleton (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift M d) i) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG.solution
