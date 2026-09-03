import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegral_and_isIntegral_pullback_of_isIntegral_pullback_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIntegral_and_isIntegral_pullback_of_isIntegral_pullback_of_isAlgClosed
    (K : Type) [Field K] (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType πX]
    (L : Type) [Field L] [IsAlgClosed L] [Algebra K L]
    (hL : IsIntegral (CategoryTheory.Limits.pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K L))))) :
    IsIntegral X ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k],
        IsIntegral (CategoryTheory.Limits.pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K k)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegral_and_isIntegral_pullback_of_isIntegral_pullback_of_isAlgClosed.solution
