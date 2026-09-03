import Mathlib
import Definitions.Def_NumberField_SUnitsModule
import P2M.Util
import P2M.Sol.S_NumberField_SUnits_finrank_groupCohomology_zero_sUnitsRep_add_one

set_option autoImplicit false
open IsDedekindDomain NumberField
theorem NumberField.SUnits.finrank_groupCohomology_zero_sUnitsRep_add_one (E K : Type) [Field E] [Field K]
    [NumberField K] [Algebra E K] (S : Finset (HeightOneSpectrum (𝓞 E))) (H : Subgroup (K ≃ₐ[E] K)) :
    Module.finrank ℤ (groupCohomology (Rep.res H.subtype (NumberField.SUnits.sUnitsRep E K S)) 0) + 1 =
      Nat.card {u : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) // u.under (𝓞 E) ∈ S} +
        Nat.card (InfinitePlace (IntermediateField.fixedField H)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SUnits_finrank_groupCohomology_zero_sUnitsRep_add_one.solution
