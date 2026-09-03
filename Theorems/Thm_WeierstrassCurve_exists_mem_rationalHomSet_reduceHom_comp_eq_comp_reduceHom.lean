import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom

theorem WeierstrassCurve.exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (IsLocalRing.ResidueField A)] (E₁ E₂ : WeierstrassCurve A) (hΔ₁ : (E₁.map (IsLocalRing.residue A)).Δ ≠ 0) (hΔ₂ : (E₂.map (IsLocalRing.residue A)).Δ ≠ 0) {μ : (E₁.map A.subtype).toAffine.Point →+ (E₂.map A.subtype).toAffine.Point} (hμ : μ ∈ WeierstrassCurve.rationalHomSet L (E₁.map A.subtype) (E₂.map A.subtype)) : ∃ ν ∈ WeierstrassCurve.rationalHomSet (IsLocalRing.ResidueField A) (E₁.map (IsLocalRing.residue A)) (E₂.map (IsLocalRing.residue A)), (WeierstrassCurve.reduceHom hΔ₂).comp μ = AddMonoidHom.comp ν (WeierstrassCurve.reduceHom hΔ₁) ∧ (μ ≠ 0 → ν ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom.solution
