import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_map_pullback_eq_of_iSup_eq_top_of_disjoint

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlueDisj

universe w₁ w₂ w₃ w₄ in

theorem mapComp'_inv_app_comp_hom_app {B : Type w₁} [Bicategory.{w₂, w₁} B] (F : Pseudofunctor B Cat.{w₃, w₄})
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (h₁ h₂ : f ≫ g = fg) (A : F.obj a) :
    (F.mapComp' f g fg h₁).inv.toNatTrans.app A ≫ (F.mapComp' f g fg h₂).hom.toNatTrans.app A = 𝟙 _ :=
  Cat.Hom.inv_hom_id_toNatTrans_app _ _

theorem subsingleton_hom_of_isEmpty {V : Scheme.{u}} [IsEmpty V] (L₁ L₂ : V.Modules) : Subsingleton (L₁ ⟶ L₂) := by
  refine ⟨fun f g => ?_⟩
  apply Scheme.Modules.hom_ext
  intro U
  have hU : U = ⊥ := by
    ext x
    exact (IsEmpty.false x).elim
  exact (TopCat.Sheaf.isTerminalOfEqEmpty ⟨_, Scheme.Modules.isSheaf L₂⟩ hU).hom_ext _ _

theorem isEmpty_of_disjoint {Y : Scheme.{u}} {U₁ U₂ : Y.Opens} (h : U₁ ⊓ U₂ = ⊥) {V : Scheme.{u}}
    (a : V ⟶ U₁) (b : V ⟶ U₂) (hab : a ≫ U₁.ι = b ≫ U₂.ι) : IsEmpty V := by
  refine ⟨fun v => ?_⟩
  have h1 : (a ≫ U₁.ι).base v ∈ (U₁ : Set Y) := by
    rw [Scheme.Hom.comp_base, TopCat.comp_app]
    exact (a.base v).2
  have h2 : (a ≫ U₁.ι).base v ∈ (U₂ : Set Y) := by
    rw [hab, Scheme.Hom.comp_base, TopCat.comp_app]
    exact (b.base v).2
  have h3 : (a ≫ U₁.ι).base v ∈ (U₁ ⊓ U₂ : Y.Opens) := ⟨h1, h2⟩
  rw [h] at h3
  exact h3

end GlueDisj

theorem solution
    {Y : Scheme.{u}} {ι : Type v} (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤)
    (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (L₁ L₂ : Y.Modules)
    (φ : ∀ i, (Scheme.Modules.pullback (U i).ι).obj L₁ ⟶ (Scheme.Modules.pullback (U i).ι).obj L₂) :
    ∃! Φ : L₁ ⟶ L₂, ∀ i, (Scheme.Modules.pullback (U i).ι).map Φ = φ i := by
  classical
  have hg : ∀ y : Y, ∃ i, y ∈ Set.range (U i).ι := by
    intro y
    have hy : y ∈ (⨆ i, U i : Y.Opens) := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact ⟨i, by rw [Scheme.Opens.range_ι]; exact hi⟩
  have bij := AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover (fun i => (U i).ι) hg L₁ L₂
  let ψ : (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData (fun i => (U i).ι)).obj L₁ ⟶
      (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData (fun i => (U i).ι)).obj L₂ :=
    { hom := φ
      comm := by
        intro V q i j a b ha hb
        by_cases hij : i = j
        · subst hij
          have hab : a = b := (cancel_mono (U i).ι).1 (ha.trans hb.symm)
          subst hab
          rw [((((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
              (fun i => (U i).ι)).obj L₂).hom_self q a ha,
            ((((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
              (fun i => (U i).ι)).obj L₁).hom_self q a ha,
            Category.comp_id, Category.id_comp]
        · haveI := GlueDisj.isEmpty_of_disjoint (hdisj i j hij) a b (ha.trans hb.symm)
          exact (GlueDisj.subsingleton_hom_of_isEmpty _ _).elim _ _ }
  obtain ⟨Φ, hΦ⟩ := bij.2 ψ
  refine ⟨Φ, fun i => ?_, fun Φ' hΦ' => ?_⟩
  · have h := congrArg (fun t => Pseudofunctor.DescentData.Hom.hom t i) hΦ
    exact h
  · apply bij.1
    rw [hΦ]
    ext i
    exact hΦ' i
