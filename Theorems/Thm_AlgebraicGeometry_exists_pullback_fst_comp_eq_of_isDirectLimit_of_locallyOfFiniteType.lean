import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {W V : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of (G i))) (v : V ⟶ Spec (CommRingCat.of (G i)))
    [QuasiCompact w] [LocallyOfFiniteType v] (a b : W ⟶ V) (ha : a ≫ v = w) (hb : b ≫ v = w)
    (hab : pullback.fst w (Spec.map (CommRingCat.ofHom (g i))) ≫ a =
      pullback.fst w (Spec.map (CommRingCat.ofHom (g i))) ≫ b) :
    ∃ (j : ι) (hij : i ≤ j),
      pullback.fst w (Spec.map (CommRingCat.ofHom (φ i j hij))) ≫ a =
        pullback.fst w (Spec.map (CommRingCat.ofHom (φ i j hij))) ≫ b := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType.solution
