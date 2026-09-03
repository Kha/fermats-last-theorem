import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) [IsSeparated f]
    (F : (pullback f f).Modules) (hF : Scheme.Modules.IsInvertible F)
    (𝒦 : A.OrderedAffineCover) (V : A.Opens) (hV : IsAffineOpen V)
    (B : Type) [CommRing B] [Algebra Γ(A, V) B]
    (t : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f)
    (hx : x.1 = Scheme.TwoAffineOpenCover.specMap Γ(A, V) B ≫ hV.fromSpec) :
    letI tV : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K) := hV.fromSpec ≫ f
    letI xV : SchemeHomOver tV f := ⟨hV.fromSpec, rfl⟩
    letI π : pullback f tV ⟶ Spec (CommRingCat.of Γ(A, V)) := pullback.snd f tV
    letI MV : (pullback f tV).Modules := (Scheme.Modules.pullback (sliceAt f xV)).obj F
    letI _ : IsAffineHom (pullback.fst f tV) := MorphismProperty.pullback_fst _ _ inferInstance
    letI _ : IsAffineHom (pullback.fst f t) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒰 : (pullback f tV).OrderedAffineCover := 𝒦.comap (pullback.fst f tV)
    letI G := OModulePresheaf.ofModules (pullback.snd f t) ((Scheme.Modules.pullback (sliceAt f x)).obj F)
    letI G' := OModulePresheaf.ofModules (pullback.snd π (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B))
      ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B))).obj MV)
    Nonempty (G.H0 (𝒦.comap (pullback.fst f t)) ≃ₗ[B] G'.H0 (𝒰.baseChange π B)) ∧
      ∀ i : ℕ, Nonempty (G.HSucc (𝒦.comap (pullback.fst f t)) i ≃ₗ[B] G'.HSucc (𝒰.baseChange π B) i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen.solution
