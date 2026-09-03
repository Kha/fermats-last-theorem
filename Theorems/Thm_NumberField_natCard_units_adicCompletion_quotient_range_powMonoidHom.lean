import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_natCard_units_adicCompletion_quotient_range_powMonoidHom
attribute [-simp] IsLocalRing.principalUnits_zero

set_option autoImplicit false
theorem NumberField.natCard_units_adicCompletion_quotient_range_powMonoidHom {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {n : ℕ} (hμ : (primitiveRoots n (v.adicCompletion K)).Nonempty) :
    Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range)
        = n ^ 2 * Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {(n : v.adicCompletionIntegers K)}) ∧
      Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_natCard_units_adicCompletion_quotient_range_powMonoidHom.solution
