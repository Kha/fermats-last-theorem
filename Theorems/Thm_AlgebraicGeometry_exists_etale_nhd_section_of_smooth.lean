import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_etale_nhd_section_of_smooth

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_etale_nhd_section_of_smooth
    {R : Type u} [CommRing R] [IsLocalRing R]
    {U : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ U)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E) (_ : Algebra.Etale R E) (𝔫 : Ideal E) (_ : 𝔫.IsMaximal)
      (h𝔫 : IsLocalRing.maximalIdeal R ≤ 𝔫.comap (algebraMap R E))
      (_ : ∀ e : E, ∃ r : R, e - algebraMap R E r ∈ 𝔫)
      (τ : Spec (CommRingCat.of E) ⟶ U),
      τ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R E)) ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔫)) ≫ τ =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap 𝔫 (algebraMap R E) h𝔫)) ≫ x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_etale_nhd_section_of_smooth.solution
