import Mathlib
import P2M.Util
import P2M.Sol.S_SlashInvariantForm_coe_trace_slash_eq_coe_trace_of_coe_eq_slash

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem SlashInvariantForm.coe_trace_slash_eq_coe_trace_of_coe_eq_slash
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex ℋ] {k : ℤ}
    {F G : Type*} [FunLike F UpperHalfPlane ℂ] [FunLike G UpperHalfPlane ℂ]
    [SlashInvariantFormClass F 𝒢 k] [SlashInvariantFormClass G 𝒢 k]
    (f : F) (g : G) (A W : GL (Fin 2) ℝ) (hg : (⇑g : UpperHalfPlane → ℂ) = (⇑f : UpperHalfPlane → ℂ) ∣[k] A)
    (hA : ∀ x ∈ 𝒢, A * x * A⁻¹ ∈ 𝒢) (hA' : ∀ x ∈ 𝒢, A⁻¹ * x * A ∈ 𝒢)
    (hW : ∀ x ∈ ℋ, W * x * W⁻¹ ∈ ℋ) (hW' : ∀ x ∈ ℋ, W⁻¹ * x * W ∈ ℋ) (hAW : A * W⁻¹ ∈ ℋ) :
    (⇑(SlashInvariantForm.trace ℋ f) : UpperHalfPlane → ℂ) ∣[k] W = ⇑(SlashInvariantForm.trace ℋ g) := by p2m_exact_reverting @_root_.P2MW.S_SlashInvariantForm_coe_trace_slash_eq_coe_trace_of_coe_eq_slash.solution
