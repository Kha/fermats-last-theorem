import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius

set_option autoImplicit false

theorem ModularCurve.qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (f : LaurentSeries K) :
    (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
      ModularCurve.qDecimate K p (f⁻¹ * ModularCurve.qEuler K f)) =
      (ModularCurve.coeffMap (frobenius K p) f)⁻¹ *
        ModularCurve.qEuler K (ModularCurve.coeffMap (frobenius K p) f) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius.solution
