import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_comp_eq_of_forall_algEquiv_comp_eq
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_comp_eq_of_forall_algEquiv_comp_eq
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (hfix : ∀ x : L, (∀ σ : L ≃ₐ[K] L, σ x = x) → ∃ a : K, algebraMap K L a = x)
    {Y : Scheme.{u}} (y : Spec (.of L) ⟶ Y)
    (hy : ∀ σ : L ≃ₐ[K] L, Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ y = y) :
    ∃ y₀ : Spec (.of K) ⟶ Y, Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ y₀ = y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_comp_eq_of_forall_algEquiv_comp_eq.solution
