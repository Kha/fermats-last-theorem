import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_exists_valuation_units_Kw

set_option autoImplicit false
open ExtCitation.LocalLevel
theorem ExtCitation.LocalLevel.exists_valuation_units_Kw (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] :
    ∃ v : (↥Kw)ˣ →* Multiplicative ℤ, Function.Surjective v ∧
      (∀ x : (↥Kw)ˣ, v x = 1 ↔ ((x : Kw) ∈ Rw q Kw ∧ ((x⁻¹ : (↥Kw)ˣ) : Kw) ∈ Rw q Kw)) ∧
      (∀ (σ : Kw ≃ₐ[ℚ_[q]] Kw) (x : (↥Kw)ˣ), v (Units.map (σ : Kw →* Kw) x) = v x) ∧
      (∀ x : (↥Kw)ˣ, (x : Kw) ∈ Rw q Kw → v x ≤ 1) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_exists_valuation_units_Kw.solution
