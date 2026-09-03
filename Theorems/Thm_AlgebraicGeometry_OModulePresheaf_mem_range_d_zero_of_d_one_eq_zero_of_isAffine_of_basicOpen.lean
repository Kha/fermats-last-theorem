import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_mem_range_d_zero_of_d_one_eq_zero_of_isAffine_of_basicOpen
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.mem_range_d_zero_of_d_one_eq_zero_of_isAffine_of_basicOpen
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsAffine X] (π : X ⟶ Spec (CommRingCat.of R))
    (𝒱 : X.OrderedAffineCover) (s : 𝒱.ι → Γ(X, ⊤)) (hs : ∀ v : 𝒱.ι, 𝒱.U v = X.basicOpen (s v))
    (z : (OModulePresheaf.unit π).cochain 𝒱 1) (hz : (OModulePresheaf.unit π).d 𝒱 1 z = 0) :
    z ∈ LinearMap.range ((OModulePresheaf.unit π).d 𝒱 0) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_range_d_zero_of_d_one_eq_zero_of_isAffine_of_basicOpen.solution
