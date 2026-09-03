import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_forall_specMap_base_mem_of_isDirectLimit

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_forall_specMap_base_mem_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) (W : (Spec (CommRingCat.of (G i))).Opens)
    (hW : ∀ p : Spec (CommRingCat.of R), (Spec.map (CommRingCat.ofHom (g i))).base p ∈ W) :
    ∃ (j : ι) (hij : i ≤ j), ∀ q : Spec (CommRingCat.of (G j)), (Spec.map (CommRingCat.ofHom (φ i j hij))).base q ∈ W := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_forall_specMap_base_mem_of_isDirectLimit.solution
