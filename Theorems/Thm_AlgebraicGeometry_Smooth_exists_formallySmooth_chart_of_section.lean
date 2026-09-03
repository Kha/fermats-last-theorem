import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_formallySmooth_chart_of_section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.Smooth.exists_formallySmooth_chart_of_section
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (hf : Smooth f)
    (s : Spec (CommRingCat.of R) ⟶ A) (hs : s ≫ f = 𝟙 _) :
    ∃ (n : ℕ) (a : Fin n → R), Ideal.span (Set.range a) = ⊤ ∧
      ∀ (i : Fin n) (Rᵢ : Type u) [CommRing Rᵢ] [Algebra R Rᵢ] [IsLocalization.Away (a i) Rᵢ],
        ∃ (g : ℕ) (B : Type u) (_ : CommRing B) (_ : Algebra Rᵢ B) (_ : Algebra.FormallySmooth Rᵢ B)
          (ε : B →ₐ[Rᵢ] Rᵢ) (x : Fin g → B)
          (ι : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C],
            (B →ₐ[Rᵢ] C) →
              SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f),

          (∀ j, ε (x j) = 0) ∧
          (RingHom.ker ε ≤ Ideal.span (Set.range x) ⊔ RingHom.ker ε ^ 2) ∧
          (∀ c : Fin g → Rᵢ, (∑ j, c j • x j) ∈ RingHom.ker ε ^ 2 → c = 0) ∧

          (∀ (C C' : Type u) [CommRing C] [Algebra Rᵢ C] [CommRing C'] [Algebra Rᵢ C']
            (ψ : C →ₐ[Rᵢ] C') (φ : B →ₐ[Rᵢ] C),
              (ι C' (ψ.comp φ)).1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (ι C φ).1) ∧

          (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C], Function.Injective (ι C)) ∧

          ((ι Rᵢ ε).1 = Spec.map (CommRingCat.ofHom (algebraMap R Rᵢ)) ≫ s) ∧

          (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C), IsNilpotent J →
            ∀ (P : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f)
              (φ₀ : B →ₐ[Rᵢ] C ⧸ J),
              (ι (C ⧸ J) φ₀).1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 →
                ∃ φ : B →ₐ[Rᵢ] C, ι C φ = P) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_formallySmooth_chart_of_section.solution
