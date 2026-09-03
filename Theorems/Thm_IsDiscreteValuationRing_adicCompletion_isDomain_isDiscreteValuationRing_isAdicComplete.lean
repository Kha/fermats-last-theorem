import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete

set_option autoImplicit false

universe u

open IsLocalRing

theorem IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
    (C : Type u) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] (ϖ : C) (hϖ : Irreducible ϖ) :
    ∃ (_ : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal C) C))
      (_ : IsDiscreteValuationRing (AdicCompletion (IsLocalRing.maximalIdeal C) C))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal C) C)) (AdicCompletion (IsLocalRing.maximalIdeal C) C)),
      Irreducible (algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) ϖ) ∧
      (∀ (n : ℕ) (c : C), algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) c ∈
          Ideal.span {algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) ϖ ^ n} → c ∈ Ideal.span {ϖ ^ n}) ∧
      (∀ (n : ℕ) (w : AdicCompletion (IsLocalRing.maximalIdeal C) C), ∃ c : C,
          w - algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) c ∈
            Ideal.span {algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) ϖ ^ n}) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete.solution
