import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.FieldTheory.IntermediateField.Basic
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem

open scoped Manifold

theorem UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ ℂ) {ι : Type*} (f : ι → UpperHalfPlane → ℂ)
    (hf : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i) ∧ ∃ m : ℕ,
      Function.Periodic ((f i * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      UpperHalfPlane.IsBoundedAtImInfty (f i * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (f i * ModularForm.discriminant ^ m)).coeff n ∈ K)
    (hli : LinearIndependent ↥K f) : LinearIndependent ℂ f := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem.solution
