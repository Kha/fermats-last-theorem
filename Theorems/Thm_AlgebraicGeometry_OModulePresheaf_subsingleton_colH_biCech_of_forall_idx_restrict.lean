import Mathlib
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_subsingleton_colH_biCech_of_forall_idx_restrict
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.subsingleton_colH_biCech_of_forall_idx_restrict
    {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (N : Z.Modules) (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent)
    (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j)) (hcov : ⨆ j, 𝔅.U j = ⊤)
    (hA : ∀ (p : ℕ) (s : 𝔄.Idx p), ∃ 𝔚 : ((𝔄.inter s : Z.Opens) : Scheme.{u}).OrderedAffineCover,
      (OModulePresheaf.ofModules ((𝔄.inter s).ι ≫ π) (N.restrict (𝔄.inter s).ι)).H0 𝔚 = ⊥ ∧
        ∀ j : ℕ, Subsingleton ((OModulePresheaf.ofModules ((𝔄.inter s).ι ≫ π) (N.restrict (𝔄.inter s).ι)).HSucc 𝔚 j))
    (p q : ℕ) :
    Subsingleton (DoubleComplex.colH ((OModulePresheaf.ofModules π N).biCech 𝔄 𝔅) p q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_colH_biCech_of_forall_idx_restrict.solution
