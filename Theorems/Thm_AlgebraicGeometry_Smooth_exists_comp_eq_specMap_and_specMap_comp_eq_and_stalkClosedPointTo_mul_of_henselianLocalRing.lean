import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing
    {R A : Type u} [CommRing R] [CommRing A] [HenselianLocalRing A] [Algebra R A]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [Smooth c]
    (xk : Spec (.of (IsLocalRing.ResidueField A)) ⟶ X)
    (hxk : xk ≫ c = Spec.map (CommRingCat.ofHom ((algebraMap A (IsLocalRing.ResidueField A)).comp (algebraMap R A)))) :
    ∃ σ : Spec (.of A) ⟶ X,
      σ ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A))) ≫ σ = xk ∧
      ∀ (r : R) (g : X.presheaf.stalk (σ.base (IsLocalRing.closedPoint A))),
        (Scheme.stalkClosedPointTo σ).hom
            ((X.presheaf.germ ⊤ (σ.base (IsLocalRing.closedPoint A)) trivial).hom
              (c.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)) * g) =
          algebraMap R A r * (Scheme.stalkClosedPointTo σ).hom g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing.solution
