import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_existsUnique_hom_app_eq_of_affHom_ofModules
attribute [-instance] AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
attribute [-simp] AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.existsUnique_hom_app_eq_of_affHom_ofModules
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M N : X.Modules)
    (Φ : OModulePresheaf.AffHom (OModulePresheaf.ofModules f M) (OModulePresheaf.ofModules f N)) :
    ∃! α : M ⟶ N, ∀ (U : X.affineOpens) (s : Γ(M, U.1)), α.app U.1 s = Φ.app U s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_hom_app_eq_of_affHom_ofModules.solution
