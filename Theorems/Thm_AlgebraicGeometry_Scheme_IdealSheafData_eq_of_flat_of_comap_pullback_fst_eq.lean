import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_flat_of_comap_pullback_fst_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.eq_of_flat_of_comap_pullback_fst_eq
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of R)) (J₁ J₂ : X.IdealSheafData)
    [Flat (J₁.subschemeι ≫ q)] [Flat (J₂.subschemeι ≫ q)]
    (h : J₁.comap (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K)))) =
      J₂.comap (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    J₁ = J₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_flat_of_comap_pullback_fst_eq.solution
