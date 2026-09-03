import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_restrict_preimage_snd_sliceAt_fromSpec
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_restrict_preimage_snd_sliceAt_fromSpec
    {k : Type u} [CommRing k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) [IsSeparated f]
    (F : (pullback f f).Modules) (hF : Scheme.Modules.IsInvertible F)
    (𝒰 : A.OrderedAffineCover) (V : A.Opens) (hV : IsAffineOpen V)
    (W : (pullback f f).Opens) (hW : W = (pullback.snd f f) ⁻¹ᵁ V)
    (𝔚 : (W : Scheme.{u}).OrderedAffineCover) :
    letI S : Type u := ↥Γ(A, V)
    letI σ : Spec (CommRingCat.of S) ⟶ A := hV.fromSpec
    letI tS : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of k) := σ ≫ f
    letI xS : SchemeHomOver tS f := ⟨σ, rfl⟩
    letI FS : (pullback f tS).Modules := (Scheme.Modules.pullback (sliceAt f xS)).obj F
    letI _ : IsAffineHom (pullback.fst f tS) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒰S : (pullback f tS).OrderedAffineCover := 𝒰.comap (pullback.fst f tS)
    letI GS := OModulePresheaf.ofModules (pullback.snd f tS) FS
    letI GW := OModulePresheaf.ofModules (W.ι ≫ pullback.fst f f ≫ f) (F.restrict W.ι)
    letI _ : Algebra k S := Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI _ : Module k ↥(GS.H0 𝒰S) := Module.compHom _ (algebraMap k S)
    letI _ : ∀ q : ℕ, Module k (GS.HSucc 𝒰S q) := fun q => Module.compHom _ (algebraMap k S)
    Nonempty (↥(GW.H0 𝔚) ≃ₗ[k] ↥(GS.H0 𝒰S)) ∧
      ∀ q : ℕ, Nonempty (GW.HSucc 𝔚 q ≃ₗ[k] GS.HSucc 𝒰S q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_restrict_preimage_snd_sliceAt_fromSpec.solution
