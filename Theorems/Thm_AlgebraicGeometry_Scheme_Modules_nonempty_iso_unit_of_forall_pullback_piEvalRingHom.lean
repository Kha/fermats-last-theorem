import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_piEvalRingHom
attribute [-instance] AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
attribute [-simp] AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_forall_pullback_piEvalRingHom
    {k : ℕ} (R : Fin k → Type u) [∀ i, CommRing (R i)]
    (N : (Spec (CommRingCat.of (∀ i, R i))).Modules)
    (h : ∀ i, Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i)))).obj N ≅
      SheafOfModules.unit (Spec (CommRingCat.of (R i))).ringCatSheaf)) :
    Nonempty (N ≅ SheafOfModules.unit (Spec (CommRingCat.of (∀ i, R i))).ringCatSheaf) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_piEvalRingHom.solution
