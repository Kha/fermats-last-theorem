import Mathlib
import Definitions.Def_TwoChartCech_GluedLines
import P2M.Util
import P2M.Sol.S_TwoChartCech_exists_linearEquiv_gluedLinesSections_of_invertible

set_option autoImplicit false

open TwoChartCech TensorProduct

universe u

theorem TwoChartCech.exists_linearEquiv_gluedLinesSections_of_invertible
    (k : Type u) [Field k] {s : ℕ} (a b : Fin s → kˣ) (ha : Function.Injective a) (hb : Function.Injective b)
    (𝒰 : Cover.{u, u} k) (S : Sections.{u, u, u} 𝒰)
    (φ₀ : 𝒰.A0 ≃ₐ[k] (gluedLinesCover k a b).A0) (φ₁ : 𝒰.A1 ≃ₐ[k] (gluedLinesCover k a b).A1)
    (φ₀₁ : 𝒰.A01 ≃ₐ[k] (gluedLinesCover k a b).A01)
    (hφ₀ : ∀ f, φ₀₁ (𝒰.ρ0 f) = (gluedLinesCover k a b).ρ0 (φ₀ f))
    (hφ₁ : ∀ f, φ₀₁ (𝒰.ρ1 f) = (gluedLinesCover k a b).ρ1 (φ₁ f))
    [Module.Invertible 𝒰.A0 S.M0] [Module.Invertible 𝒰.A1 S.M1] :
    letI : Algebra 𝒰.A0 𝒰.A01 := 𝒰.ρ0.toRingHom.toAlgebra
    letI : Algebra 𝒰.A1 𝒰.A01 := 𝒰.ρ1.toRingHom.toAlgebra
    ∀ (rbc0 : 𝒰.A01 ⊗[𝒰.A0] S.M0 ≃ₗ[𝒰.A01] S.M01) (rbc1 : 𝒰.A01 ⊗[𝒰.A1] S.M1 ≃ₗ[𝒰.A01] S.M01),
      (∀ t, rbc0 ((1 : 𝒰.A01) ⊗ₜ[𝒰.A0] t) = S.r0 t) →
      (∀ t, rbc1 ((1 : 𝒰.A01) ⊗ₜ[𝒰.A1] t) = S.r1 t) →
      ∃ (n m : ℤ) (lam : Fin s → kˣ)
        (e₀ : S.M0 ≃ₗ[k] (gluedLinesSections k a b lam n m).M0)
        (e₁ : S.M1 ≃ₗ[k] (gluedLinesSections k a b lam n m).M1)
        (e₀₁ : S.M01 ≃ₗ[k] (gluedLinesSections k a b lam n m).M01),
        (∀ t, e₀₁ (S.r0 t) = (gluedLinesSections k a b lam n m).r0 (e₀ t)) ∧
        (∀ t, e₀₁ (S.r1 t) = (gluedLinesSections k a b lam n m).r1 (e₁ t)) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_exists_linearEquiv_gluedLinesSections_of_invertible.solution
