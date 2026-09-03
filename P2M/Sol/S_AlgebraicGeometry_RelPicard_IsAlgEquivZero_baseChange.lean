import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_baseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem solution
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) {L : A.Modules} (hL : IsAlgEquivZero a L) :
    IsAlgEquivZero (pullback.snd a (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      ((Scheme.Modules.pullback (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj L) := by
  obtain ⟨T', h, hft, hgi, M, hM, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := hL
  set ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K)) with hι

  set aK : Limits.pullback a ι ⟶ Spec (CommRingCat.of K) := pullback.snd a ι with haK
  set hK : Limits.pullback h ι ⟶ Spec (CommRingCat.of K) := pullback.snd h ι with hhK
  haveI : LocallyOfFiniteType hK := MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ hft
  haveI : GeometricallyIntegral hK := MorphismProperty.pullback_snd (P := @GeometricallyIntegral) _ _ hgi

  let φ : Limits.pullback aK hK ⟶ Limits.pullback a h :=
    pullback.lift (pullback.fst aK hK ≫ pullback.fst a ι) (pullback.snd aK hK ≫ pullback.fst h ι) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc]
      congr 1
      exact pullback.condition.symm)

  let ψ : Limits.pullback aK (𝟙 (Spec (CommRingCat.of K))) ⟶ Limits.pullback a (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.lift (pullback.fst aK (𝟙 _) ≫ pullback.fst a ι) (pullback.snd aK (𝟙 _) ≫ ι) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, Category.comp_id, Category.id_comp])

  let tK : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h → SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) hK :=
    fun tt => ⟨pullback.lift (ι ≫ tt.1) (𝟙 _) (by rw [Category.assoc, tt.2, Category.comp_id, Category.id_comp]),
      by rw [hhK, pullback.lift_snd]⟩
  have hsq : ∀ tt : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h,
      baseChangeSnd aK (tK tt) ≫ φ = ψ ≫ baseChangeSnd a tt := by
    intro tt
    apply pullback.hom_ext <;>
      simp only [φ, ψ, tK, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]
  have hfst : ψ ≫ pullback.fst a (𝟙 _) = pullback.fst aK (𝟙 _) ≫ pullback.fst a ι := by
    simp only [ψ, pullback.lift_fst]
  refine ⟨Limits.pullback h ι, hK, inferInstance, inferInstance, (Scheme.Modules.pullback φ).obj M, hM.pullback φ,
    tK t₀, tK t₁, ⟨?_⟩, ⟨?_⟩⟩
  · exact (Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (hsq t₀)).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback ψ).mapIso e₀ ≪≫
      Scheme.Modules.pullbackUnitIso ψ
  · exact (Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (hsq t₁)).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback ψ).mapIso e₁ ≪≫
      (Scheme.Modules.pullbackComp _ _).app L ≪≫
      (Scheme.Modules.pullbackCongr hfst).app L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L).symm ≪≫
      Iso.refl _
