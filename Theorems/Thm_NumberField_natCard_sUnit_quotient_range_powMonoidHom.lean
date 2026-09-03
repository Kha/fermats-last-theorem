import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_natCard_sUnit_quotient_range_powMonoidHom

set_option autoImplicit false
theorem NumberField.natCard_sUnit_quotient_range_powMonoidHom (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite S]
    {n : ℕ} (hμ : (primitiveRoots n K).Nonempty) :
    Nat.card (↥(S.unit K) ⧸ (powMonoidHom n : ↥(S.unit K) →* ↥(S.unit K)).range)
      = n ^ (Nat.card S + NumberField.Units.rank K + 1) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_natCard_sUnit_quotient_range_powMonoidHom.solution
