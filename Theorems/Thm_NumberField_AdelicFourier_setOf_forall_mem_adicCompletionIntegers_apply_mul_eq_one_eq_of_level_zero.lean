import Definitions.Def_NumberField_AdelicFourier
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one_eq_of_level_zero

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.AdelicFourier.setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one_eq_of_level_zero
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) ℂ)
    (h0 : ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ z = 1)
    (h1 : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψ x ≠ 1) :
    {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1} =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one_eq_of_level_zero.solution
