import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.nonempty_HEquiv_pi {R : Type u} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] (D : ι → ProjSpaceCech.GradedModule R n) (i : ℕ) :
    Nonempty (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.pi D) i ≃ₗ[R] (∀ k, ProjSpaceCech.GradedModule.H (D k) i)) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi.solution
