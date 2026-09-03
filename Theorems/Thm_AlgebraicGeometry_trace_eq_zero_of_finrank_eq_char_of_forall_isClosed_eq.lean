import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_trace_eq_zero_of_finrank_eq_char_of_forall_isClosed_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.trace_eq_zero_of_finrank_eq_char_of_forall_isClosed_eq
    {κ : Type u} [Field κ] [IsAlgClosed κ] {p : ℕ} [Fact p.Prime] [CharP κ p]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (fY : Y ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType fY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (hrk : ∀ y, f.finrank y = p)
    (hinj : ∀ x₁ x₂ : X, IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → f.base x₁ = f.base x₂ → x₁ = x₂)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    ∀ [Module.Free Γ(Y, U) Γ(X, f ⁻¹ᵁ U)] [Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U)],
      Algebra.trace Γ(Y, U) Γ(X, f ⁻¹ᵁ U) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_trace_eq_zero_of_finrank_eq_char_of_forall_isClosed_eq.solution
