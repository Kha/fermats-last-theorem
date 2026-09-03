import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_ideal_pow_le_of_forall_le_radical

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_forall_ideal_pow_le_of_forall_le_radical
    {X : Scheme.{u}} [IsNoetherian X] (𝓙₁ 𝓙₂ : X.IdealSheafData)
    (h : ∀ U : X.affineOpens, 𝓙₁.ideal U ≤ (𝓙₂.ideal U).radical) :
    ∃ t : ℕ, ∀ U : X.affineOpens, 𝓙₁.ideal U ^ t ≤ 𝓙₂.ideal U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_ideal_pow_le_of_forall_le_radical.solution
