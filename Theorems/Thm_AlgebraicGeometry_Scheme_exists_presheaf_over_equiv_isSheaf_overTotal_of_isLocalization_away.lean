import Mathlib
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite Limits

theorem AlgebraicGeometry.Scheme.exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away
    (R : Type) [CommRing R]
    (F : ∀ (A : Type) [CommRing A] [Algebra R A], Type)
    (Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B)
    (Fmap_id : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), Fmap A A (AlgHom.id R A) s = s)
    (Fmap_comp : ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B]
      [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (s : F A),
      Fmap A C (ψ.comp φ) s = Fmap B C ψ (Fmap A B φ s))
    (sheaf : ∀ (A : Type) [CommRing A] [Algebra R A] (n : ℕ) (f : Fin n → A),
      Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra R (B i)]
        [∀ i, IsScalarTower R A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, F (B i)),
      (∀ (i j : Fin n) (C : Type) [CommRing C] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
          [IsLocalization.Away (f i * f j) C] (ρ₁ : B i →ₐ[A] C) (ρ₂ : B j →ₐ[A] C),
          Fmap _ _ (ρ₁.restrictScalars R) (s i) = Fmap _ _ (ρ₂.restrictScalars R) (s j)) →
      ∃! s₀ : F A, ∀ i, Fmap _ _ (IsScalarTower.toAlgHom R A (B i)) s₀ = s i) :
    ∃ (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type)
      (ev : ∀ (A : Type) [CommRing A] [Algebra R A],
        F A ≃ G.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))))),
      Presheaf.IsSheaf Scheme.zariskiTopology G.overTotal ∧
      ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (s : F A)
        (h : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
          Spec.map (CommRingCat.ofHom (algebraMap R B))),
        ev B (Fmap A B φ s) =
          G.map (Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) h :
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))).op (ev A s) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_presheaf_over_equiv_isSheaf_overTotal_of_isLocalization_away.solution
