import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated
    {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated g]
    (φ ψ : X ⟶ Y) (hφ : φ ≫ g = f) (hψ : ψ ≫ g = f)
    (h : ∀ x : Spec (CommRingCat.of Ω) ⟶ X,
      x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) → x ≫ φ = x ≫ ψ) :
    φ = ψ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated.solution
