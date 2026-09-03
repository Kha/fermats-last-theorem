import Mathlib
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite Limits

theorem AlgebraicGeometry.Scheme.exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart
    (R : Type) [CommRing R]
    (F : ∀ (A : Type) [CommRing A] [Algebra R A], Type)
    (Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B)
    (Fmap_id : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), Fmap A A (AlgHom.id R A) s = s)
    (Fmap_comp : ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B]
      [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (s : F A),
      Fmap A C (ψ.comp φ) s = Fmap B C ψ (Fmap A B φ s))
    (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type)
    (ev : ∀ (A : Type) [CommRing A] [Algebra R A],
      F A ≃ G.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))))))
    (hG : Presheaf.IsSheaf Scheme.zariskiTopology G.overTotal)
    (hev : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (s : F A)
      (h : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
        Spec.map (CommRingCat.ofHom (algebraMap R B))),
      ev B (Fmap A B φ s) =
        G.map (Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) h :
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))).op (ev A s))
    (ι : Type) (P : ι → ∀ (A : Type) [CommRing A] [Algebra R A], F A → Prop)
    (isOpen : ∀ (i : ι) (A : Type) [CommRing A] [Algebra R A] (s : F A),
      ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
        ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
          P i B (Fmap A B φ s) ↔ Set.range (PrimeSpectrum.comap φ.toRingHom) ⊆ U)
    (S : ι → Type) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (chart : ∀ (i : ι) (A : Type) [CommRing A] [Algebra R A], {s : F A // P i A s} ≃ (S i →ₐ[R] A))
    (chart_natural : ∀ (i : ι) (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (φ : A →ₐ[R] B) (s : {s : F A // P i A s}) (h : P i B (Fmap A B φ s.1)),
      chart i B ⟨Fmap A B φ s.1, h⟩ = φ.comp (chart i A s))
    (cover : ∀ (K : Type) [Field K] [Algebra R K] (s : F K), ∃ i, P i K s) :
    ∃ f : ∀ i, yoneda.obj (Spec (CommRingCat.of (S i))) ⟶ G.overTotal,
      (∀ i, IsOpenImmersion.presheaf (f i)) ∧
      Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) ∧
      ∀ i, (f i).app (op (Spec (CommRingCat.of (S i)))) (𝟙 (Spec (CommRingCat.of (S i)))) =
        ⟨Spec.map (CommRingCat.ofHom (algebraMap R (S i))),
          ev (S i) ((chart i (S i)).symm (AlgHom.id R (S i))).1⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_presheaf_overTotal_of_isOpen_of_chart.solution
