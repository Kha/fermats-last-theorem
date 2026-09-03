import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_PointAddEquivOfEq
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq

theorem WeierstrassCurve.exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (IsLocalRing.ResidueField A)] (E' : WeierstrassCurve A) (hΔ' : (E'.map (IsLocalRing.residue A)).Δ ≠ 0) {V : WeierstrassCurve (IsLocalRing.ResidueField A)} (v : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField A)) (hv : v • E'.map (IsLocalRing.residue A) = V) : ∃ (E : WeierstrassCurve A) (hΔ : (E.map (IsLocalRing.residue A)).Δ ≠ 0) (hred : E.map (IsLocalRing.residue A) = V), ∃ θ ∈ WeierstrassCurve.rationalHomSet L (E'.map A.subtype) (E.map A.subtype), ∃ θ' ∈ WeierstrassCurve.rationalHomSet L (E.map A.subtype) (E'.map A.subtype), θ'.comp θ = AddMonoidHom.id _ ∧ θ.comp θ' = AddMonoidHom.id _ ∧ ∀ P : (E'.map A.subtype).toAffine.Point, WeierstrassCurve.pointAddEquivOfEq hred (WeierstrassCurve.reduceHom hΔ (θ P)) = (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ' P) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq.solution
