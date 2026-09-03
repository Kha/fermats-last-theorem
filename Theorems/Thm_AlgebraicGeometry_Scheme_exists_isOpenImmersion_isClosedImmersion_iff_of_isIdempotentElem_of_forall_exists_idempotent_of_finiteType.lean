import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType
    (R : Type) [CommRing R]
    (F : ∀ (B : Type) [CommRing B] [Algebra R B], Type)
    (Fmap : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'], (B →ₐ[R] B') → F B → F B')
    (H : Scheme.{0}) (pH : H ⟶ Spec (CommRingCat.of R)) (hH : LocallyOfFiniteType pH)
    (pt : ∀ (B : Type) [CommRing B] [Algebra R B],
      F B ≃ {g : Spec (CommRingCat.of B) ⟶ H // g ≫ pH = Spec.map (CommRingCat.ofHom (algebraMap R B))})
    (hpt : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B') (x : F B),
      (pt B' (Fmap B B' φ x)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt B x).1)
    (P : ∀ (B : Type) [CommRing B] [Algebra R B], F B → Prop)
    (hP : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] (x : F B), ∃ e : B, IsIdempotentElem e ∧
      ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'), P B' (Fmap B B' φ x) ↔ φ e = 1) :
    ∃ (X : Scheme.{0}) (ι : X ⟶ H), IsOpenImmersion ι ∧ IsClosedImmersion ι ∧
      ∀ (B : Type) [CommRing B] [Algebra R B] (x : F B) (e : B), IsIdempotentElem e →
        (∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'), P B' (Fmap B B' φ x) ↔ φ e = 1) →
        (P B x ↔ ∃ g : Spec (CommRingCat.of B) ⟶ X, g ≫ ι = (pt B x).1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType.solution
