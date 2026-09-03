import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq
    (K : Type*) [Field K] (N : ℕ) [NeZero N] {S : Type*} [DivisionRing S]
    (φ ψ : ↥(modularFunctionFieldC K N) →+* S)
    (hK : ∀ a : K, φ (algebraMap K ↥(modularFunctionFieldC K N) a) = ψ (algebraMap K ↥(modularFunctionFieldC K N) a))
    (hj : φ (jGeomGen K N) = ψ (jGeomGen K N)) (hjN : φ (jNGeomGen K N) = ψ (jNGeomGen K N)) :
    φ = ψ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq.solution
