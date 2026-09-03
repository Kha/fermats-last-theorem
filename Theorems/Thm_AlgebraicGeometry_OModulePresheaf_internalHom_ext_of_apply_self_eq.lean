import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.internalHom_ext_of_apply_self_eq
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}
    (hFq : F.IsQuasicoherent) (hGq : G.IsQuasicoherent) (U : V.affineOpens)
    (φ ψ : (OModulePresheaf.internalHom F G).obj U.1)
    (h : ∀ x : F.obj U.1, φ.1 ⟨U, le_rfl⟩ x = ψ.1 ⟨U, le_rfl⟩ x) : φ = ψ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq.solution
