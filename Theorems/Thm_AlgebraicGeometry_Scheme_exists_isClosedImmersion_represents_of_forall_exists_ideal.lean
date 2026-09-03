import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isClosedImmersion_represents_of_forall_exists_ideal
    (R : Type) [CommRing R]
    (F : ∀ (A : Type) [CommRing A] [Algebra R A], Type)
    (Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B)
    (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
      F A ≃ {g : Spec (CommRingCat.of A) ⟶ X // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
    (pt_natural : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (φ : A →ₐ[R] B) (s : F A),
      (pt B (Fmap A B φ s)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A s).1)
    (W : ∀ (A : Type) [CommRing A] [Algebra R A], F A → Prop)
    (closed : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), ∃ 𝔞 : Ideal A,
      ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
        W B (Fmap A B φ s) ↔ ∀ a ∈ 𝔞, φ a = 0) :
    ∃ (Z : Scheme.{0}) (ι : Z ⟶ X)
      (ptZ : ∀ (A : Type) [CommRing A] [Algebra R A],
        {s : F A // W A s} ≃
          {g : Spec (CommRingCat.of A) ⟶ Z //
            g ≫ ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))}),
      IsClosedImmersion ι ∧
      ∀ (A : Type) [CommRing A] [Algebra R A] (s : {s : F A // W A s}),
        (ptZ A s).1 ≫ ι = (pt A s.1).1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.solution
