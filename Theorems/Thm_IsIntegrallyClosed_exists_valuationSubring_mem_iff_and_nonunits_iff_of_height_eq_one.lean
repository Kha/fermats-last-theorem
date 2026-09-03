import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one

set_option autoImplicit false

theorem IsIntegrallyClosed.exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one
    {C K : Type*} [CommRing C] [IsDomain C] [IsNoetherianRing C] [IsIntegrallyClosed C]
    [Field K] [Algebra C K] [IsFractionRing C K]
    (P : Ideal C) [P.IsPrime] (hP : P.height = 1) :
    ∃ V : ValuationSubring K,
      (∀ x : K, x ∈ V ↔ ∃ c s : C, s ∉ P ∧ x * algebraMap C K s = algebraMap C K c) ∧
      (∀ c : C, algebraMap C K c ∈ V) ∧
      (∀ c : C, algebraMap C K c ∈ V.nonunits ↔ c ∈ P) ∧
      (∀ ϖ : C, ϖ ∈ P →
        ((∀ f : K, f ∈ V.nonunits → ∃ g : K, g ∈ V ∧ f = algebraMap C K ϖ * g) ↔
          IsLocalRing.maximalIdeal (Localization.AtPrime P) =
            Ideal.span {algebraMap C (Localization.AtPrime P) ϖ})) ∧
      ∃ ι : IsLocalRing.ResidueField ↥V ≃+* P.ResidueField,
        ∀ (c : C) (hc : algebraMap C K c ∈ V),
          ι (IsLocalRing.residue ↥V ⟨algebraMap C K c, hc⟩) = algebraMap C P.ResidueField c := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one.solution
