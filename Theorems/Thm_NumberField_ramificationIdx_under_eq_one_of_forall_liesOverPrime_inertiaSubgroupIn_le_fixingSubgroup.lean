import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
open NumberField
open scoped NumberField

set_option autoImplicit false

theorem NumberField.ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
    (K : Type) [Field K] [NumberField K]
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (φL : K →ₐ[ℚ] L)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hHin : ∀ P : ValuationSubring (AlgebraicClosure ℚ),
      P.LiesOverPrime ℓ → P.inertiaSubgroupIn ℚ ≤ L.fixingSubgroup) :
    letI : Algebra K L := φL.toRingHom.toAlgebra
    ∀ Q : Ideal (𝓞 L), Q.IsMaximal → (ℓ : 𝓞 L) ∈ Q →
      Ideal.ramificationIdx' (Q.under (𝓞 K)) Q = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.solution
