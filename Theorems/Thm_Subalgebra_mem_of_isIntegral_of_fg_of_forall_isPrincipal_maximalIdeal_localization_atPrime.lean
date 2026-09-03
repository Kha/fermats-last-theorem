import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import P2M.Util
import P2M.Sol.S_Subalgebra_mem_of_isIntegral_of_fg_of_forall_isPrincipal_maximalIdeal_localization_atPrime

set_option autoImplicit false

theorem Subalgebra.mem_of_isIntegral_of_fg_of_forall_isPrincipal_maximalIdeal_localization_atPrime
    {κ : Type*} [Field κ] {E : Type*} [Field E] [Algebra κ E]
    (M : Subalgebra κ E) (hfg : M.FG)
    (hfrac : ∀ u : E, ∃ d ∈ M, d ≠ 0 ∧ u * d ∈ M)
    (hprin : ∀ (𝔪 : Ideal M) [𝔪.IsMaximal],
      (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)).IsPrincipal)
    (u : E) (hu : IsIntegral M u) : u ∈ M := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_mem_of_isIntegral_of_fg_of_forall_isPrincipal_maximalIdeal_localization_atPrime.solution
