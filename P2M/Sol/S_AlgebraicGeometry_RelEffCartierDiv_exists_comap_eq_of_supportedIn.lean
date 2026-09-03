import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_comap_eq_of_supportedIn

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {𝒳 S : Scheme.{u}} {c : 𝒳 ⟶ S} (U : 𝒳.Opens) {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv c r g) (hD : D.SupportedIn U) :
    ∃ D' : RelEffCartierDiv (U.ι ≫ c) r g,
      D'.I = D.I.comap (pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp)) := by

  set j := pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp) with hj
  have hrange : Set.range ⇑j = (pullback.fst c g) ⁻¹' (U : Set 𝒳) := by
    rw [hj, Scheme.Pullback.range_map]
    simp [Scheme.Opens.range_ι]
  have hjsnd : j ≫ pullback.snd c g = pullback.snd (U.ι ≫ c) g := by
    rw [hj, pullback.lift_snd, Category.comp_id]

  set Z := D.I.subscheme with hZ
  let ι := D.I.subschemeι

  have hZU : ∀ z : Z, ι z ∈ Set.range ⇑j := by
    intro z
    rw [hrange, Set.mem_preimage]
    have hz : ι z ∈ (D.I.support : Set ↥(pullback c g)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
    exact hD hz

  haveI : IsIso (pullback.snd j ι) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    ext z
    simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [Scheme.Pullback.range_snd]
    exact hZU z

  let e : (D.I.comap j).subscheme ⟶ Z := (D.I.comapIso j).hom ≫ pullback.snd j ι
  haveI : IsIso e := IsIso.comp_isIso
  have hfac : (D.I.comap j).subschemeι ≫ pullback.snd (U.ι ≫ c) g = e ≫ (ι ≫ pullback.snd c g) := by
    rw [← hjsnd, ← Scheme.IdealSheafData.comapIso_hom_fst]
    simp only [Category.assoc]
    rw [pullback.condition_assoc]
    rfl
  haveI := D.isFinite; haveI := D.flat; haveI := D.locallyOfFinitePresentation
  refine ⟨{ I := D.I.comap j
            isFinite := by rw [hfac]; infer_instance
            flat := by rw [hfac]; infer_instance
            locallyOfFinitePresentation := by rw [hfac]; infer_instance
            finrank_eq := fun t => by
              rw [hfac, Scheme.Hom.finrank_comp_left_of_isIso]
              exact D.finrank_eq t }, rfl⟩
