import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.Scheme.exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization
    {R : Type} [CommRing R] [IsNoetherianRing R] {M : Scheme.{0}} (ϖ : M ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType ϖ] (x : ↥M) (hx : IsClosed ({x} : Set ↥M)) :
    ∃ (n : ℕ) (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) (hJ : J.IsMaximal)
      (hJI : (J.map (Ideal.Quotient.mk I)).IsPrime)
      (ι : Spec (CommRingCat.of (MvPolynomial (Fin n) R ⧸ I)) ⟶ M) (_ : IsOpenImmersion ι),
      ι ≫ ϖ = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I))) ∧
      ι.base ⟨J.map (Ideal.Quotient.mk I), hJI⟩ = x ∧
      (Algebra.FormallySmooth R (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) →
          (ϖ.stalkMap x).hom.FormallySmooth) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization.solution
