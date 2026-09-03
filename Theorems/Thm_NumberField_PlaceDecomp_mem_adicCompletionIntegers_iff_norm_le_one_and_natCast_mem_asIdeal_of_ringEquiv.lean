import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
set_option autoImplicit false
open NumberField IsDedekindDomain

theorem NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
    (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    (Φ : w.adicCompletion F ≃+* L') :
    (∀ y : w.adicCompletion F, y ∈ w.adicCompletionIntegers F ↔ ‖((Φ y : ↥L') : PadicAlgCl q)‖ ≤ 1) ∧
      ((q : ℕ) : 𝓞 F) ∈ w.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv.solution
