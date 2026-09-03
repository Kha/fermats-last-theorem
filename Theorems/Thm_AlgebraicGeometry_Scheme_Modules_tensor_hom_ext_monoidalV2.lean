import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_tensor_hom_ext_monoidalV2

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.tensor_hom_ext_monoidalV2
    {X : Scheme.{u}} {M P N : X.Modules} {θ θ' : M ⊗ P ⟶ N}
    (h : ∀ (U : X.Opens) (m : Γ(M, U)) (p : Γ(P, U)),
      θ.app U (AlgebraicGeometry.Scheme.Modules.tensorSections m p) =
        θ'.app U (AlgebraicGeometry.Scheme.Modules.tensorSections m p)) :
    θ = θ' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_tensor_hom_ext_monoidalV2.solution
