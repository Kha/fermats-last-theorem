import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor NeronModelInfra
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.HilbertFunctor.exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg
    (R : Type) [CommRing R] (n : ℕ) (h : ℕ → ℕ)
    (hbc : ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (P : Point A n h),
        ∃ Q : Point B n h, Q.I = Ideal.map (MvPolynomial.map φ) P.I)
    (Hilb : Scheme.{0}) (πH : Hilb ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (A : Type) [CommRing A] (ψ : R →+* A),
      Point A n h ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom ψ)) πH)
    (hnat : ∀ (A B : Type) [CommRing A] [CommRing B] (ψ : R →+* A) (φ : A →+* B) (P : Point A n h) (Q : Point B n h),
        Q.I = Ideal.map (MvPolynomial.map φ) P.I →
        (pt B (φ.comp ψ) Q).1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt A ψ P).1)
    (I₀ : Ideal (MvPolynomial (Fin (n + 1)) R)) (hI₀ : ∀ p ∈ I₀, ∀ d : ℕ, homogeneousComponent d p ∈ I₀)
    (hfg : I₀.FG) (m : ℕ) :
    ∃ (C : Scheme.{0}) (ι : C ⟶ Hilb), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
      ∀ (A : Type) [CommRing A] (ψ : R →+* A) (P : Point A n h),
        (∃ c : Spec (CommRingCat.of A) ⟶ C, c ≫ ι = (pt A ψ P).1) ↔
          ∀ (d : ℕ), m ≤ d → ∀ F : MvPolynomial (Fin (n + 1)) A,
            F ∈ Ideal.map (MvPolynomial.map ψ) I₀ → F.IsHomogeneous d → F ∈ P.I := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg.solution
