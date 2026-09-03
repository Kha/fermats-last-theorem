import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_variableChange_eq_of_forall_equivOfVariableChangeEq_eq

open WeierstrassCurve WeierstrassCurve.Affine

universe u
theorem WeierstrassCurve.Affine.variableChange_eq_of_forall_equivOfVariableChangeEq_eq
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]
    {C C' : WeierstrassCurve.VariableChange F} (hC : C • W₂ = W₁) (hC' : C' • W₂ = W₁)
    (h : ∀ P : W₁.Point, Point.equivOfVariableChangeEq hC P = Point.equivOfVariableChangeEq hC' P) :
    C = C' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_variableChange_eq_of_forall_equivOfVariableChangeEq_eq.solution
