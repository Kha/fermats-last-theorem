import Definitions.Def_AlgebraicGeometry_TwoChartCech
import P2M.Util
import P2M.Sol.S_TwoChartCech_Sections_nonempty_linearEquiv_H0_and_H1_of_linearEquiv

set_option autoImplicit false

universe u v v' w w'

open TwoChartCech

theorem TwoChartCech.Sections.nonempty_linearEquiv_H0_and_H1_of_linearEquiv
    {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} {𝒰' : Cover.{u, v'} R}
    (S : Sections.{u, v, w} 𝒰) (S' : Sections.{u, v', w'} 𝒰')
    (e₀ : S.M0 ≃ₗ[R] S'.M0) (e₁ : S.M1 ≃ₗ[R] S'.M1) (e₀₁ : S.M01 ≃ₗ[R] S'.M01)
    (h₀ : ∀ m : S.M0, e₀₁ (S.r0 m) = S'.r0 (e₀ m)) (h₁ : ∀ m : S.M1, e₀₁ (S.r1 m) = S'.r1 (e₁ m)) :
    (Nonempty (↥S.H0 ≃ₗ[R] ↥S'.H0) ∧ Nonempty (S.H1 ≃ₗ[R] S'.H1)) ∧
      Module.finrank R ↥S.H0 = Module.finrank R ↥S'.H0 ∧ (Subsingleton S.H1 ↔ Subsingleton S'.H1) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_Sections_nonempty_linearEquiv_H0_and_H1_of_linearEquiv.solution
