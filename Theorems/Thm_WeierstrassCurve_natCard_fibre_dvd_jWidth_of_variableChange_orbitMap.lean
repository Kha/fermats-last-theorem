import Mathlib
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natCard_fibre_dvd_jWidth_of_variableChange_orbitMap

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.natCard_fibre_dvd_jWidth_of_variableChange_orbitMap
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (h2 : ringChar K ≠ 2) (h3 : ringChar K ≠ 3)
    (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N] {α : Type*}
    (f : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} → α)
    (hf : ∀ H H', f H = f H' ↔ ∃ γ : VariableChange K, γ • W = W ∧
      ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ W.toAffine T) T')
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    Nat.card {H' : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} //
        f H' = f H} ∣ ModularCurve.jWidth W.j := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natCard_fibre_dvd_jWidth_of_variableChange_orbitMap.solution
