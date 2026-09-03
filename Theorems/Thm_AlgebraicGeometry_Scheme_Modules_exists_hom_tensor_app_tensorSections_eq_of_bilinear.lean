import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensor_app_tensorSections_eq_of_bilinear

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_hom_tensor_app_tensorSections_eq_of_bilinear
    {X : Scheme.{u}} (L M P : X.Modules)
    (B : ∀ U : X.Opens, Γ(L, U) →ₗ[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(P, U))
    (hB : ∀ {U V : X.Opens} (i : V ⟶ U) (s : Γ(L, U)) (t : Γ(M, U)),
      P.presheaf.map i.op (B U s t) = B V (L.presheaf.map i.op s) (M.presheaf.map i.op t)) :
    ∃ ν : L ⊗ M ⟶ P, ∀ (U : X.Opens) (s : Γ(L, U)) (t : Γ(M, U)),
      ν.app U (Scheme.Modules.tensorSections s t) = B U s t := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensor_app_tensorSections_eq_of_bilinear.solution
