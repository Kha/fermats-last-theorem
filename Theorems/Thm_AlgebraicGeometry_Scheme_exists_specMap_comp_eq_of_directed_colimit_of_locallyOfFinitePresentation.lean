import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_specMap_comp_eq_of_directed_colimit_of_locallyOfFinitePresentation

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_specMap_comp_eq_of_directed_colimit_of_locallyOfFinitePresentation
    (ι : Type u) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (S : ι → Type u) [∀ i, CommRing (S i)]
    (t : ∀ i j, i ≤ j → (S i →+* S j))
    (ht₁ : ∀ i (h : i ≤ i), t i i h = RingHom.id (S i))
    (ht₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk))
    (L : Type u) [CommRing L] (c : ∀ i, S i →+* L)
    (hc : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i)
    (hcsurj : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x)
    (hcker : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z)
    (i : ι) {Z : Scheme.{u}} (ζ : Z ⟶ Spec (CommRingCat.of (S i))) [IsAffineHom ζ] [LocallyOfFinitePresentation ζ]
    (z : Spec (CommRingCat.of L) ⟶ Z) (hz : z ≫ ζ = Spec.map (CommRingCat.ofHom (c i))) :
    ∃ (j : ι) (hij : i ≤ j) (zj : Spec (CommRingCat.of (S j)) ⟶ Z),
      zj ≫ ζ = Spec.map (CommRingCat.ofHom (t i j hij)) ∧ z = Spec.map (CommRingCat.ofHom (c j)) ≫ zj := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_specMap_comp_eq_of_directed_colimit_of_locallyOfFinitePresentation.solution
