import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_eq_comp_hom_pullback_specMap_of_isDirectLimit_of_locallyOfFinitePresentation

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_eq_comp_hom_pullback_specMap_of_isDirectLimit_of_locallyOfFinitePresentation
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {W V : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of (G i))) (v : V ⟶ Spec (CommRingCat.of (G i)))
    [QuasiCompact w] [QuasiSeparated w] [LocallyOfFinitePresentation v]
    (a : pullback w (Spec.map (CommRingCat.ofHom (g i))) ⟶ V)
    (ha : a ≫ v = pullback.fst w (Spec.map (CommRingCat.ofHom (g i))) ≫ w) :
    ∃ (j : ι) (hij : i ≤ j) (aⱼ : pullback w (Spec.map (CommRingCat.ofHom (φ i j hij))) ⟶ V),
      aⱼ ≫ v = pullback.fst w (Spec.map (CommRingCat.ofHom (φ i j hij))) ≫ w ∧
      ∀ κ : pullback w (Spec.map (CommRingCat.ofHom (g i))) ⟶ pullback w (Spec.map (CommRingCat.ofHom (φ i j hij))),
        κ ≫ pullback.fst w (Spec.map (CommRingCat.ofHom (φ i j hij))) =
          pullback.fst w (Spec.map (CommRingCat.ofHom (g i))) →
        κ ≫ pullback.snd w (Spec.map (CommRingCat.ofHom (φ i j hij))) =
          pullback.snd w (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g j)) →
        a = κ ≫ aⱼ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_eq_comp_hom_pullback_specMap_of_isDirectLimit_of_locallyOfFinitePresentation.solution
