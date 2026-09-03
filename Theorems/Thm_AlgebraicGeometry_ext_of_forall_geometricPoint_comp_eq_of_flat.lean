import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ext_of_forall_geometricPoint_comp_eq_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.ext_of_forall_geometricPoint_comp_eq_of_flat
    {R : Type u} [CommRing R] [IsDomain R] {K : Type u} [Field K] [IsAlgClosed K]
    (ι : R →+* K) (hι : Function.Injective ι)
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [LocallyOfFinitePresentation f]
    [IsReduced X] (g : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated g]
    {φ ψ : X ⟶ Y} (hφ : φ ≫ g = f) (hψ : ψ ≫ g = f)
    (h : ∀ x : Spec (CommRingCat.of K) ⟶ X,
      x ≫ f = Spec.map (CommRingCat.ofHom ι) → x ≫ φ = x ≫ ψ) :
    φ = ψ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ext_of_forall_geometricPoint_comp_eq_of_flat.solution
