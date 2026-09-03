import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_algHom_retraction_stalk_and_ker_le_span_sup_sq_of_section_of_smoothOfRelativeDimension_one

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_algHom_retraction_stalk_and_ker_le_span_sup_sq_of_section_of_smoothOfRelativeDimension_one
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 c]
    (σ : Spec (CommRingCat.of R) ⟶ X) (hσ : σ ≫ c = 𝟙 _)
    (s : Spec (CommRingCat.of R)) (hs : IsClosed ({s} : Set (Spec (CommRingCat.of R)))) :
    letI : Algebra R (X.presheaf.stalk (σ.base s)) := ((X.presheaf.germ ⊤ (σ.base s) trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    ∃ (π : X.presheaf.stalk (σ.base s) →ₐ[R] R) (t : X.presheaf.stalk (σ.base s)),

      RingHom.ker (Scheme.Hom.stalkMap σ s).hom ≤ RingHom.ker π ∧
      π t = 0 ∧ (RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2) ∧
      Module.Finite (X.presheaf.stalk (σ.base s)) Ω[(X.presheaf.stalk (σ.base s))⁄R] := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_algHom_retraction_stalk_and_ker_le_span_sup_sq_of_section_of_smoothOfRelativeDimension_one.solution
