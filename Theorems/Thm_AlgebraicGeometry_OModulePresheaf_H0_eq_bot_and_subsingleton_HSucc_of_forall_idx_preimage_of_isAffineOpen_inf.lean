import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_forall_idx_preimage_of_isAffineOpen_inf
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_forall_idx_preimage_of_isAffineOpen_inf
    {R : Type u} [CommRing R] {P Y : Scheme.{u}} (π : P ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (q : P ⟶ Y) (𝔙 : Y.OrderedAffineCover) (hVV : ∀ i j, IsAffineOpen (𝔙.U i ⊓ 𝔙.U j))
    (N : P.Modules) (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent)
    (hV : ∀ (i : ℕ) (s : 𝔙.Idx i), ∃ 𝔚 : ((q ⁻¹ᵁ 𝔙.inter s : P.Opens) : Scheme.{u}).OrderedAffineCover,
      (OModulePresheaf.ofModules ((q ⁻¹ᵁ 𝔙.inter s).ι ≫ π) (N.restrict (q ⁻¹ᵁ 𝔙.inter s).ι)).H0 𝔚 = ⊥ ∧
        ∀ j : ℕ, Subsingleton ((OModulePresheaf.ofModules ((q ⁻¹ᵁ 𝔙.inter s).ι ≫ π) (N.restrict (q ⁻¹ᵁ 𝔙.inter s).ι)).HSucc 𝔚 j))
    (𝔚 : P.OrderedAffineCover) :
    (OModulePresheaf.ofModules π N).H0 𝔚 = ⊥ ∧ ∀ j : ℕ, Subsingleton ((OModulePresheaf.ofModules π N).HSucc 𝔚 j) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_forall_idx_preimage_of_isAffineOpen_inf.solution
