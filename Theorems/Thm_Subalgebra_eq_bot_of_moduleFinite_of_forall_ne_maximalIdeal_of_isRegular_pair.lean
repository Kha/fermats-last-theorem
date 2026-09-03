import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_eq_bot_of_moduleFinite_of_forall_ne_maximalIdeal_of_isRegular_pair

set_option autoImplicit false

theorem Subalgebra.eq_bot_of_moduleFinite_of_forall_ne_maximalIdeal_of_isRegular_pair
    {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (R : Subalgebra B (Localization (nonZeroDivisors B))) [Module.Finite B ↥R]
    (ha : ∀ (𝔮 : Ideal B) [𝔮.IsPrime], 𝔮 ≠ IsLocalRing.maximalIdeal B →
      ∀ r ∈ R, ∃ s : B, s ∉ 𝔮 ∧ (algebraMap B (Localization (nonZeroDivisors B)) s) * r ∈
        (algebraMap B (Localization (nonZeroDivisors B))).range)
    (hb : ∃ a b : B, a ∈ IsLocalRing.maximalIdeal B ∧ b ∈ IsLocalRing.maximalIdeal B ∧
      RingTheory.Sequence.IsRegular B [a, b]) :
    R = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_eq_bot_of_moduleFinite_of_forall_ne_maximalIdeal_of_isRegular_pair.solution
