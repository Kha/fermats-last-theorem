import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_tilde
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_tilde {R : CommRingCat.{u}}
    (P : ModuleCat.{u} R) [Module.Finite R P] [Module.Projective R P] (n : ℕ)
    (hrk : ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P) = n) :
    Scheme.Modules.IsLocallyFreeOfRank n (tilde P) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_tilde.solution
