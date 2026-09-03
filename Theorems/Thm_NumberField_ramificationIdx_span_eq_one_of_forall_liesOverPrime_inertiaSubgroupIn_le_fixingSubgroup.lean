import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
open NumberField
open scoped NumberField

set_option autoImplicit false

theorem NumberField.ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hHin : ∀ P : ValuationSubring (AlgebraicClosure ℚ),
      P.LiesOverPrime ℓ → P.inertiaSubgroupIn ℚ ≤ L.fixingSubgroup) :
    ∀ Q : Ideal (𝓞 L), Q.IsMaximal → (ℓ : 𝓞 L) ∈ Q →
      Ideal.ramificationIdx' (Ideal.span {(ℓ : ℤ)}) Q = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.solution
