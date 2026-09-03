import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isInvertible_tilde_of_projective_rankOne
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.isInvertible_tilde_of_projective_rankOne
    {R : CommRingCat.{u}} (P : ModuleCat.{u} R) [Module.Finite R P] [Module.Projective R P]
    (hrk : ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P) = 1) :
    Scheme.Modules.IsInvertible (tilde P) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_tilde_of_projective_rankOne.solution
