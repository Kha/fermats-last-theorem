import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_natCard_units_adicCompletionIntegers_quotient_range_powMonoidHom
attribute [-simp] IsLocalRing.principalUnits_zero

set_option autoImplicit false
theorem NumberField.natCard_units_adicCompletionIntegers_quotient_range_powMonoidHom {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {n : ℕ} (hμ : (primitiveRoots n (v.adicCompletion K)).Nonempty) :
    Nat.card ((v.adicCompletionIntegers K)ˣ ⧸
        (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →* (v.adicCompletionIntegers K)ˣ).range)
      = n * Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {(n : v.adicCompletionIntegers K)}) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_natCard_units_adicCompletionIntegers_quotient_range_powMonoidHom.solution
