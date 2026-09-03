import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_diamondActionModL_apply_eq_self_of_coe_eq_coeffMap_modularUnitSeries
attribute [-simp] ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

theorem ModularCurve.diamondActionModL_apply_eq_self_of_coe_eq_coeffMap_modularUnitSeries
    (p : ℕ) [Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (d : CongruenceSubgroup.Gamma0 N)
    (x : LaurentSeries ℤ)
    (hx : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p)
    (g : ↥(qExpFunctionFieldC κ (CohCarrier.GammaH N H'))) (hg : ((g : ↥(qExpFunctionFieldC κ (CohCarrier.GammaH N H'))) : LaurentSeries κ) = coeffMap (Int.castRingHom κ) x) :
    diamondActionModL κ N H' d g = g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diamondActionModL_apply_eq_self_of_coe_eq_coeffMap_modularUnitSeries.solution
