import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_smoothOfRelativeDimension_restrict_subscheme_vanishingIdeal_of_isOpenImmersion

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.IdealSheafData.smoothOfRelativeDimension_restrict_subscheme_vanishingIdeal_of_isOpenImmersion
    {X S : Scheme.{u}} (s : X ⟶ S) (Y : Closeds X) (hY : (Y : Set X) ∈ irreducibleComponents X)
    (A : Type u) [CommRing A] (g : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion g] (n : ℕ)
    (hP : ∀ P : Ideal A, P ∈ minimalPrimes A → PrimeSpectrum.zeroLocus (P : Set A) = g.base ⁻¹' (Y : Set X) →
      SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) ≫ g ≫ s)) :
    SmoothOfRelativeDimension n
      (((Scheme.IdealSheafData.vanishingIdeal Y).subschemeι ⁻¹ᵁ g.opensRange).ι ≫
        (Scheme.IdealSheafData.vanishingIdeal Y).subschemeι ≫ s) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_smoothOfRelativeDimension_restrict_subscheme_vanishingIdeal_of_isOpenImmersion.solution
