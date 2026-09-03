import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_integralClosure_le_and_exists_ideal_mem_iff_mem_nonunits_and_mem_iff_exists_of_isDiscreteValuationRing

set_option autoImplicit false

universe u

open scoped Pointwise

theorem ValuationSubring.integralClosure_le_and_exists_ideal_mem_iff_mem_nonunits_and_mem_iff_exists_of_isDiscreteValuationRing
    {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type u) [Field K] [Algebra C K] [IsFractionRing C K]
    {M : Type u} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ IsLocalRing.maximalIdeal C) :
    (∀ b : ↥(integralClosure C M), (b : M) ∈ V) ∧
    ∃ P : Ideal ↥(integralClosure C M), P.IsMaximal ∧ P.LiesOver (IsLocalRing.maximalIdeal C) ∧
      (∀ b : ↥(integralClosure C M), b ∈ P ↔ (b : M) ∈ V.nonunits) ∧
      (∀ y : M, y ∈ V ↔ ∃ b s : ↥(integralClosure C M), s ∉ P ∧ y * (s : M) = (b : M)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_integralClosure_le_and_exists_ideal_mem_iff_mem_nonunits_and_mem_iff_exists_of_isDiscreteValuationRing.solution
