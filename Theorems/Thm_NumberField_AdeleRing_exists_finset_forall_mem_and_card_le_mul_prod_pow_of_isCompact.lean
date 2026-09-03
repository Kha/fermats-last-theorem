import Mathlib.NumberTheory.NumberField.AdeleRing
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec

set_option autoImplicit false

open scoped NumberField

theorem NumberField.AdeleRing.exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact
    (K : Type) [Field K] [NumberField K]
    {B : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)} (hB : IsCompact B) :
    ∃ M : ℝ, ∀ (a : NumberField.AdeleRing (𝓞 K) K) (R : NumberField.InfinitePlace K → ℝ),
      ∃ s : Finset K,
        (∀ k : K, (algebraMap K (NumberField.AdeleRing (𝓞 K) K) k - a).2 ∈ B →
          (∀ w : NumberField.InfinitePlace K,
            ‖(algebraMap K (NumberField.AdeleRing (𝓞 K) K) k - a).1 w‖ ≤ R w) → k ∈ s) ∧
        (s.card : ℝ) ≤ M * ∏ w : NumberField.InfinitePlace K, max 1 (R w) ^ w.mult := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact.solution
