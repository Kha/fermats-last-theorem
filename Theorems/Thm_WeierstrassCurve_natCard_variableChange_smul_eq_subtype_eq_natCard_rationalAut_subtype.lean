import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natCard_variableChange_smul_eq_subtype_eq_natCard_rationalAut_subtype

set_option autoImplicit false

theorem WeierstrassCurve.natCard_variableChange_smul_eq_subtype_eq_natCard_rationalAut_subtype
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (Q : (W.toAffine.Point → W.toAffine.Point) → Prop) :
    Nat.card {C : WeierstrassCurve.VariableChange κ //
        ∃ hC : C • W = W, Q (fun P => WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hC P)} =
      Nat.card {ι : W.toAffine.Point →+ W.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ W W ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ W W, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        Q ι} := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natCard_variableChange_smul_eq_subtype_eq_natCard_rationalAut_subtype.solution
