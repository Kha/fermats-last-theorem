import Mathlib
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_eq_smul_of_forall_eq_inv_smul_pow
import Theorems.Thm_ModularCurve_qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow
import P2M.Util
namespace P2MW.S_ModularCurve_qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul

set_option autoImplicit false

open AlgebraicCurve
open scoped MatrixGroups

theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [PerfectField K] (Γ : Subgroup SL(2, ℤ))
    (w : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K Γ)) :
    ModularCurve.qExpFrobeniusPlaceModL K Γ p w = ModularCurve.qExpArithFrobC p K Γ • w :=
  AlgebraicCurve.Place.restrictAlong_eq_smul_of_forall_eq_inv_smul_pow p (Fact.out : p.Prime).ne_zero
    (ModularCurve.qExpArithFrobC p K Γ) (ModularCurve.qExpFrobeniusModL K Γ p)
    (ModularCurve.qExpFrobeniusModL_isIntegral K Γ p)
    (ModularCurve.qExpFrobeniusModL_eq_inv_qExpArithFrobC_smul_pow p K Γ) w

#print axioms solution
