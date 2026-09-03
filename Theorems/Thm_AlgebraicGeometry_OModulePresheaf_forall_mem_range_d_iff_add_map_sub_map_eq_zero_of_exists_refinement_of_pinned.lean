import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_forall_mem_range_d_iff_add_map_sub_map_eq_zero_of_exists_refinement_of_pinned
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.forall_mem_range_d_iff_add_map_sub_map_eq_zero_of_exists_refinement_of_pinned
    {κ : Type u} [Field κ] {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of κ)) [IsSeparated πX]
    (𝒦 : X.OrderedAffineCover) (ψ : X ⟶ X)

    (R : Type u) [CommRing R] [Algebra κ R] (ev : R →+* κ)
    (W : Type u) [AddCommGroup W] [Module κ W]
    (Φ : ∀ (M : Type u) [AddCommGroup M] [Module κ M], ↥(Algebra.PointDerivations κ R ev (M)) ≃ₗ[κ] (W ⊗[κ] M))
    (hΦnat : ∀ (M M' : Type u) [AddCommGroup M] [Module κ M] [AddCommGroup M'] [Module κ M'] (g : M →ₗ[κ] M')
        (δ : ↥(Algebra.PointDerivations κ R ev (M))),
        Φ M' (Algebra.PointDerivations.map ev g δ) = TensorProduct.map (LinearMap.id : W →ₗ[κ] W) g (Φ M δ))
    (V : Type u) [AddCommGroup V] [Module κ V]

    (H₁ : Type u) [AddCommGroup H₁] [Module κ H₁]
    (cls₁ : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)) →ₗ[κ] H₁)
    (hcls₁0 : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)), cls₁ z = 0 ↔ (z : (OModulePresheaf.unit πX).cochain 𝒦 1) ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒦 0))
    (ρψ : H₁ →ₗ[κ] H₁)
    (hρψ : ∀ (𝒱 : X.OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒦.ι)
        (hl : ∀ v, 𝒱.U v ≤ ψ ⁻¹ᵁ 𝒦.U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam' v))
        (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1))),
        OModulePresheaf.unitPullback (πX := πX) ψ 𝒱 𝒦 lam hl (0 + 1) z.1 -
            OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱 𝒦 lam' hl' (0 + 1) z'.1 ∈
          LinearMap.range ((OModulePresheaf.unit πX).d 𝒱 0) →
        ρψ (cls₁ z) = cls₁ z')
    (θψ : W →ₗ[κ] W)

    (c c₀ c' : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)))
    (ĉ ĉ₀ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))))
    (hĉ : ∀ (a : R) (ξ : Module.Dual κ V), ((ĉ.1 a ξ).1 : (OModulePresheaf.unit πX).cochain 𝒦 1) = c.1 a ξ)
    (hĉ₀ : ∀ (a : R) (ξ : Module.Dual κ V), ((ĉ₀.1 a ξ).1 : (OModulePresheaf.unit πX).cochain 𝒦 1) = c₀.1 a ξ)
    (hc'Z : ∀ (a : R) (ξ : Module.Dual κ V), (OModulePresheaf.unit πX).d 𝒦 1 (c'.1 a ξ) = 0)

    (hrel : ∃ (𝒱₀ : X.OrderedAffineCover) (lam₀ lam₀' : 𝒱₀.ι → 𝒦.ι)
      (hl₀ : ∀ v, 𝒱₀.U v ≤ ψ ⁻¹ᵁ 𝒦.U (lam₀ v)) (hl₀' : ∀ v, 𝒱₀.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam₀' v)),
      ∀ (a : R) (ξ : Module.Dual κ V),
        ∃ b : (OModulePresheaf.unit πX).cochain 𝒱₀ 0,
          (OModulePresheaf.unit πX).d 𝒱₀ 0 b =
            OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (c'.1 a ξ)
              - OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (c₀.1 a ξ)
              - OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (((Φ (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1) →ₗ[κ] (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)) (Φ (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1) c))).1 a ξ)
              + OModulePresheaf.unitPullback (πX := πX) ψ 𝒱₀ 𝒦 lam₀ hl₀ 1 (c.1 a ξ)) :
    (∀ (a : R) (ξ : Module.Dual κ V), c'.1 a ξ ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒦 0)) ↔
      (Φ (Module.Dual κ V →ₗ[κ] H₁) (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev (LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)) H₁ cls₁) ĉ₀) +
          (TensorProduct.map θψ (LinearMap.id : (Module.Dual κ V →ₗ[κ] H₁) →ₗ[κ] (Module.Dual κ V →ₗ[κ] H₁))
              (Φ (Module.Dual κ V →ₗ[κ] H₁) (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev (LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)) H₁ cls₁) ĉ)) -
            TensorProduct.map (LinearMap.id : W →ₗ[κ] W) (LinearMap.llcomp κ (Module.Dual κ V) H₁ H₁ ρψ)
              (Φ (Module.Dual κ V →ₗ[κ] H₁) (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev (LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)) H₁ cls₁) ĉ))) = 0) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_mem_range_d_iff_add_map_sub_map_eq_zero_of_exists_refinement_of_pinned.solution
