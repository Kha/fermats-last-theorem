import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_pullback_fst_snd_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (𝒦 : A.OrderedAffineCover) (μ : pullback f f ⟶ A) (hμ : μ ≫ f = pullback.fst f f ≫ f) :
    ∃ (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒦.ι),
      (∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒦.U (lam₁ w)) ∧
      (∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒦.U (lam₂ w)) ∧
      (∀ w, 𝒲.U w ≤ μ ⁻¹ᵁ 𝒦.U (lam₃ w)) := by
  classical
  have mem_cover : ∀ y : A, ∃ i, y ∈ 𝒦.U i := fun y => by
    have hy : y ∈ (⊤ : A.Opens) := trivial
    rw [← 𝒦.iSup_eq_top] at hy
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  have box : ∀ i j : 𝒦.ι, IsAffineOpen (pullback.fst f f ⁻¹ᵁ 𝒦.U i ⊓ pullback.snd f f ⁻¹ᵁ 𝒦.U j) :=
    fun i j => (Scheme.Pullback.isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
      f f (𝒦.U i) (𝒦.isAffineOpen i) (𝒦.U j) (𝒦.isAffineOpen j)).1

  let γ : pullback f f ⟶ pullback (μ ≫ f) f := pullback.lift (𝟙 _) μ (Category.id_comp (μ ≫ f))
  haveI : IsClosedImmersion γ := inferInstance
  have box3 : ∀ i j l : 𝒦.ι,
      IsAffineOpen (pullback.fst f f ⁻¹ᵁ 𝒦.U i ⊓ pullback.snd f f ⁻¹ᵁ 𝒦.U j ⊓ μ ⁻¹ᵁ 𝒦.U l) := by
    intro i j l
    have h2 := (Scheme.Pullback.isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
      (μ ≫ f) f _ (box i j) (𝒦.U l) (𝒦.isAffineOpen l)).1
    have h3 := h2.preimage γ
    have e : γ ⁻¹ᵁ (pullback.fst (μ ≫ f) f ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ 𝒦.U i ⊓ pullback.snd f f ⁻¹ᵁ 𝒦.U j) ⊓
        pullback.snd (μ ≫ f) f ⁻¹ᵁ 𝒦.U l) =
        pullback.fst f f ⁻¹ᵁ 𝒦.U i ⊓ pullback.snd f f ⁻¹ᵁ 𝒦.U j ⊓ μ ⁻¹ᵁ 𝒦.U l := by
      rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.lift_fst,
        pullback.lift_snd, Scheme.Hom.id_preimage]
    rwa [e] at h3
  refine ⟨{ ι := 𝒦.ι × 𝒦.ι × 𝒦.ι
            instLinearOrder := (inferInstance : LinearOrder (𝒦.ι ×ₗ 𝒦.ι ×ₗ 𝒦.ι))
            U := fun w => pullback.fst f f ⁻¹ᵁ 𝒦.U w.1 ⊓ pullback.snd f f ⁻¹ᵁ 𝒦.U w.2.1 ⊓ μ ⁻¹ᵁ 𝒦.U w.2.2
            isAffineOpen := fun w => box3 w.1 w.2.1 w.2.2
            iSup_eq_top := ?_ }, fun w => w.1, fun w => w.2.1, fun w => w.2.2, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := mem_cover ((pullback.fst f f).base x)
    obtain ⟨j, hj⟩ := mem_cover ((pullback.snd f f).base x)
    obtain ⟨l, hl⟩ := mem_cover (μ.base x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j, l), ⟨⟨hi, hj⟩, hl⟩⟩
  · intro w; exact inf_le_left.trans inf_le_left
  · intro w; exact inf_le_left.trans inf_le_right
  · intro w; exact inf_le_right
