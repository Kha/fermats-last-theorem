import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_finite_locallyPrincipalOverring

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_finite_locallyPrincipalOverring
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K₀ : Type*) [Field K₀] [Algebra C K₀] [IsFractionRing C K₀]
    {κ : Type*} [Field κ] [Algebra K₀ κ] [Algebra C κ] [IsScalarTower C K₀ κ] [FiniteDimensional K₀ κ]
    [Algebra.IsSeparable K₀ κ]
    {A : Type*} [CommRing A] [Algebra C A] [Algebra A κ] [IsScalarTower C A κ] :
    ∃ D₁ : Subalgebra A κ, Module.Finite A D₁ ∧ (∀ x : κ, IsIntegral C x → x ∈ D₁) ∧
      ∀ 𝔫 : Ideal D₁, 𝔫.IsMaximal → ∃ t ∈ 𝔫, ∀ x ∈ 𝔫, ∃ s ∉ 𝔫, ∃ y : D₁, s * x = t * y := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_finite_locallyPrincipalOverring.solution
