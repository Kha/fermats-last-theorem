import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_pow_eq_of_section_fromNormalization_kummer

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.exists_pow_eq_of_section_fromNormalization_kummer
    {X : Scheme.{u}} [IsIntegral X] (k : ℕ) (g : X.functionField) (hg : g ≠ 0)
    (s : X ⟶ (Spec.map (CommRingCat.ofHom (algebraMap X.functionField
        (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).normalization)
    (hs : s ≫ (Spec.map (CommRingCat.ofHom (algebraMap X.functionField
        (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).fromNormalization = 𝟙 X) :
    ∃ f : X.functionField, f ^ k = g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_pow_eq_of_section_fromNormalization_kummer.solution
