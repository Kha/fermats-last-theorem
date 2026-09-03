import Mathlib
import P2M.Util
namespace P2MW.S_WeierstrassCurve_variableChange_mk_neg_one_smul_eq_self

set_option autoImplicit false

open WeierstrassCurve

theorem solution
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange R) • W = W := by
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, inv_neg_one, inv_one, Units.val_neg, Units.val_one] <;> ring
