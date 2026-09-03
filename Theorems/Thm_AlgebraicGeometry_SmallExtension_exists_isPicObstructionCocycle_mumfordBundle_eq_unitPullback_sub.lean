import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_mumfordBundle_eq_unitPullback_sub
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection

set_option autoImplicit false

open AlgebraicGeometry.Polarisation NeronModelInfra GoodReductionJacobian CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.exists_isPicObstructionCocycle_mumfordBundle_eq_unitPullback_sub
    {B₁ B₀ : Type u} [CommRing B₁] [CommRing B₀] (π : B₁ →+* B₀) {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    (hJ : ∀ v w : V, ι v * ι w = 0)

    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) (L : RelativeGroupLaw B₁ f)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (L₀ : RelativeGroupLaw B₀ f₀)
    (g : X₀ ⟶ X) [IsAffineHom g] (hgf : g ≫ f = f₀ ≫ Spec.map (CommRingCat.ofHom π))
    (hL₀ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ g =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom π))
          ⟨P.1 ≫ g, by rw [Category.assoc, hgf, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hgf, ← Category.assoc, Q.2]⟩).1)
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of k)) (Lk : RelativeGroupLaw k fk)
    (σ : B₁ →+* k) (i : Xk ⟶ X) [IsAffineHom i] (hif : i ≫ f = fk ≫ Spec.map (CommRingCat.ofHom σ))
    (hLk : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t fk),
      (Lk.mul t P Q).1 ≫ i =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom σ))
          ⟨P.1 ≫ i, by rw [Category.assoc, hif, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ i, by rw [Category.assoc, hif, ← Category.assoc, Q.2]⟩).1)

    (gXX : pullback f₀ f₀ ⟶ pullback f f) [IsAffineHom gXX]
    (hg₁ : gXX ≫ pullback.fst f f = pullback.fst f₀ f₀ ≫ g) (hg₂ : gXX ≫ pullback.snd f f = pullback.snd f₀ f₀ ≫ g)
    (iXX : pullback fk fk ⟶ pullback f f) [IsAffineHom iXX]
    (hi₁ : iXX ≫ pullback.fst f f = pullback.fst fk fk ≫ i) (hi₂ : iXX ≫ pullback.snd f f = pullback.snd fk fk ≫ i)

    (𝒰 : X.OrderedAffineCover)
    (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒰.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒰.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒰.U (lam₂ w))
    (h₃ : ∀ w, 𝒲.U w ≤ addMor f L ⁻¹ᵁ 𝒰.U (lam₃ w))
    (hk₁ : ∀ w, (𝒲.comap iXX).U w ≤ pullback.fst fk fk ⁻¹ᵁ (𝒰.comap i).U (lam₁ w))
    (hk₂ : ∀ w, (𝒲.comap iXX).U w ≤ pullback.snd fk fk ⁻¹ᵁ (𝒰.comap i).U (lam₂ w))
    (hk₃ : ∀ w, (𝒲.comap iXX).U w ≤ addMor fk Lk ⁻¹ᵁ (𝒰.comap i).U (lam₃ w))

    (𝓛₀ : X₀.Modules) (c : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2)
    (hc : IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c) :
    ∃ C : Module.Dual k V →ₗ[k] (OModulePresheaf.unit (pullback.fst fk fk ≫ fk)).cochain (𝒲.comap iXX) 2,
      (∀ ξ : Module.Dual k V,
        C ξ = OModulePresheaf.unitPullback (πX := pullback.fst fk fk ≫ fk) (addMor fk Lk) (𝒲.comap iXX) (𝒰.comap i) lam₃ hk₃ 2 (c ξ)
              - OModulePresheaf.unitPullback (πX := pullback.fst fk fk ≫ fk) (pullback.fst fk fk) (𝒲.comap iXX) (𝒰.comap i) lam₁ hk₁ 2 (c ξ)
              - OModulePresheaf.unitPullback (πX := pullback.fst fk fk ≫ fk) (pullback.snd fk fk) (𝒲.comap iXX) (𝒰.comap i) lam₂ hk₂ 2 (c ξ)) ∧
      IsPicObstructionCocycle V ι (pullback.fst f f ≫ f) (pullback.fst fk fk ≫ fk) iXX gXX 𝒲
        (mumfordBundle f₀ L₀ 𝓛₀) C := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_mumfordBundle_eq_unitPullback_sub.solution
