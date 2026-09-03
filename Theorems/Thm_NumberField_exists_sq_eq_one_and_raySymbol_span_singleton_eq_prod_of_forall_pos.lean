import Mathlib
import Definitions.Def_NarrowRayClassGroup
import P2M.Util
import P2M.Sol.S_NumberField_exists_sq_eq_one_and_raySymbol_span_singleton_eq_prod_of_forall_pos

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply
open scoped nonZeroDivisors

theorem NumberField.exists_sq_eq_one_and_raySymbol_span_singleton_eq_prod_of_forall_pos
    (K : Type*) [Field K] [NumberField K] {M : Type*} [CommGroup M]
    (ψ : HeightOneSpectrum (𝓞 K) → M) (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (hψ : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 → (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      raySymbol K ψ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1) :
    ∃ ε : (K →+* ℝ) → M, (∀ φ : K →+* ℝ, ε φ ^ 2 = 1) ∧
      ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
        raySymbol K ψ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) =
          ∏ φ ∈ Finset.univ.filter (fun φ : K →+* ℝ => φ (algebraMap (𝓞 K) K α) < 0), ε φ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_sq_eq_one_and_raySymbol_span_singleton_eq_prod_of_forall_pos.solution
