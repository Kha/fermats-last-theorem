import Mathlib
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natCard_torsionOrbit_bot_variableChange_eq_jWidthChar

set_option autoImplicit false

open WeierstrassCurve.Affine open WeierstrassCurve hiding natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728

theorem WeierstrassCurve.natCard_torsionOrbit_bot_variableChange_eq_jWidthChar
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hM : 4 ≤ M) (hMK : (M : K) ≠ 0)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (s : {s : Set E₀.toAffine.Point // ∃ P : E₀.toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
              T = (u : ZMod M).val • P}}) :
    Nat.card {s' : {s : Set E₀.toAffine.Point // ∃ P : E₀.toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
              T = (u : ZMod M).val • P}} //
        ∃ γ : VariableChange K, γ • E₀ = E₀ ∧
          ∀ T ∈ s'.1, ∃ T' ∈ s.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'}
      = ModularCurve.jWidthChar p E₀.j := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natCard_torsionOrbit_bot_variableChange_eq_jWidthChar.solution
