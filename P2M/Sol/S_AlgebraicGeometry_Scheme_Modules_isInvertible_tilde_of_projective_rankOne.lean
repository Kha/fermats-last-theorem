import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_tilde
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_tilde_of_projective_rankOne
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem solution {R : CommRingCat.{u}} (P : ModuleCat.{u} R) [Module.Finite R P] [Module.Projective R P]
    (hrk : ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P) = 1) :
    Scheme.Modules.IsInvertible (tilde P) :=
  (AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible (tilde P)).mp
    (AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_tilde P 1 hrk)
