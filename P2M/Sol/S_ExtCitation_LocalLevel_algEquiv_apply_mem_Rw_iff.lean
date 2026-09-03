import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
namespace P2MW.S_ExtCitation_LocalLevel_algEquiv_apply_mem_Rw_iff

set_option autoImplicit false
open ExtCitation.LocalLevel

open scoped NNReal

namespace Ws26T4D
open ExtCitation.LocalLevel

variable (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

theorem mem_Rw_iff_norm_le_one (x : Kw) : x ∈ Rw q Kw ↔ ‖(x : PadicAlgCl q)‖ ≤ 1 := by
  rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, PadicAlgCl.valuation_def]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

theorem norm_coe_eq_spectralNorm (x : Kw) : ‖(x : PadicAlgCl q)‖ = spectralNorm ℚ_[q] Kw x := by
  rw [spectralNorm.eq_of_tower (L := PadicAlgCl q), PadicAlgCl.spectralNorm_eq]; rfl

end Ws26T4D

open Ws26T4D ExtCitation.LocalLevel in
theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]
    (σ : Kw ≃ₐ[ℚ_[q]] Kw) (x : Kw) : σ x ∈ Rw q Kw ↔ x ∈ Rw q Kw := by
  rw [mem_Rw_iff_norm_le_one, mem_Rw_iff_norm_le_one, norm_coe_eq_spectralNorm, norm_coe_eq_spectralNorm,
    ← spectralNorm_eq_of_equiv σ x]
