import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import P2M.Util
import P2M.Sol.S_ProjSpaceCech_GradedModule_Hom_secMap_injective

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Hom.secMap_injective {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap) (I : Finset (Fin (n + 1))) :
    Function.Injective (ProjSpaceCech.GradedModule.Hom.secMap φ I) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_Hom_secMap_injective.solution
