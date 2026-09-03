import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natCard_stabilizer_torsionOrbit_bot_eq_two
attribute [-instance] ModularCurve.Gamma0Pair.isElliptic
attribute [-simp] ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.natCard_stabilizer_torsionOrbit_bot_eq_two
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hM : 4 ≤ M) (hMK : (M : K) ≠ 0)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (s : {s : Set E₀.toAffine.Point // ∃ P : E₀.toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
              T = (u : ZMod M).val • P}}) :
    Nat.card {γ : ↥(MulAction.stabilizer (WeierstrassCurve.VariableChange K) E₀) //
        ∀ T ∈ s.1, ∃ T' ∈ s.1, HEq (Point.vcInvFun (γ : WeierstrassCurve.VariableChange K) E₀.toAffine T) T'} = 2 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natCard_stabilizer_torsionOrbit_bot_eq_two.solution
