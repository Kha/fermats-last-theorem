import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_baseChange_of_isInvertible_of_flat
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_baseChange_of_isInvertible_of_flat
    {B : Type u} [CommRing B] {P : Scheme.{u}} (ϖ : P ⟶ Spec (CommRingCat.of B)) [IsSeparated ϖ]
    (𝔚 : P.OrderedAffineCover)
    (hflat : ∀ (i : ℕ) (s : 𝔚.Idx i),
      letI := Scheme.TwoAffineOpenCover.algebraOfHom ϖ (𝔚.inter s); Module.Flat B Γ(P, 𝔚.inter s))
    (N : P.Modules) (hN : Scheme.Modules.IsInvertible N)
    (h0 : (OModulePresheaf.ofModules ϖ N).H0 𝔚 = ⊥)
    (hS : ∀ i, Subsingleton ((OModulePresheaf.ofModules ϖ N).HSucc 𝔚 i))
    (A : Type u) [CommRing A] [Algebra B A] :
    (OModulePresheaf.ofModules (Limits.pullback.snd ϖ (Scheme.TwoAffineOpenCover.specMap B A))
        ((Scheme.Modules.pullback (Limits.pullback.fst ϖ (Scheme.TwoAffineOpenCover.specMap B A))).obj N)).H0
        (𝔚.baseChange ϖ A) = ⊥ ∧
      ∀ i, Subsingleton
        ((OModulePresheaf.ofModules (Limits.pullback.snd ϖ (Scheme.TwoAffineOpenCover.specMap B A))
          ((Scheme.Modules.pullback (Limits.pullback.fst ϖ (Scheme.TwoAffineOpenCover.specMap B A))).obj N)).HSucc
          (𝔚.baseChange ϖ A) i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_baseChange_of_isInvertible_of_flat.solution
