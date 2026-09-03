import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_comp_eq_comp
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_comp_eq_comp
    {R R' : Type u} [CommRing R] [CommRing R'] {P X : Scheme.{u}}
    (πP : P ⟶ Spec (CommRingCat.of R')) [IsSeparated πP] [CompactSpace P]
    (πX : X ⟶ Spec (CommRingCat.of R))
    (q : P ⟶ X) (G : P ⟶ P) (φ : X ⟶ X) (hG : G ≫ q = q ≫ φ)
    (𝒦 : X.OrderedAffineCover) (𝒲 : P.OrderedAffineCover) (lamq : 𝒲.ι → 𝒦.ι)
    (hq : ∀ w, 𝒲.U w ≤ q ⁻¹ᵁ 𝒦.U (lamq w))

    (𝒱 : X.OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒦.ι)
    (hl : ∀ v, 𝒱.U v ≤ φ ⁻¹ᵁ 𝒦.U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam' v))
    (n : ℕ) (z z' : (OModulePresheaf.unit πX).cochain 𝒦 n)
    (hz : (OModulePresheaf.unit πX).d 𝒦 n z = 0) (hz' : (OModulePresheaf.unit πX).d 𝒦 n z' = 0)
    (hzz' : OModulePresheaf.unitPullback (πX := πX) φ 𝒱 𝒦 lam hl n z -
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱 𝒦 lam' hl' n z'
      ∈ (show Submodule R ((OModulePresheaf.unit πX).cochain 𝒱 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒱 m)))

    (𝒱' : P.OrderedAffineCover) (mu mu' : 𝒱'.ι → 𝒲.ι)
    (hm : ∀ v, 𝒱'.U v ≤ G ⁻¹ᵁ 𝒲.U (mu v)) (hm' : ∀ v, 𝒱'.U v ≤ (𝟙 P) ⁻¹ᵁ 𝒲.U (mu' v)) :
    OModulePresheaf.unitPullback (πX := πP) G 𝒱' 𝒲 mu hm n
        (OModulePresheaf.unitPullback (πX := πP) q 𝒲 𝒦 lamq hq n z) -
        OModulePresheaf.unitPullback (πX := πP) (𝟙 P) 𝒱' 𝒲 mu' hm' n
          (OModulePresheaf.unitPullback (πX := πP) q 𝒲 𝒦 lamq hq n z')
      ∈ (show Submodule R' ((OModulePresheaf.unit πP).cochain 𝒱' n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πP).d 𝒱' m)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_comp_eq_comp.solution
