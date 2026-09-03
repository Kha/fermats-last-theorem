import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import P2M.Util
import P2M.Sol.S_ModularCurve_IsModuliPlaceOf_mem_toValuationSubring_of_isIntegral_jModElt

set_option autoImplicit false

universe u

theorem ModularCurve.IsModuliPlaceOf.mem_toValuationSubring_of_isIntegral_jModElt
    (K : Type u) [Field K] [DecidableEq K] (N : ℕ) [NeZero N]
    (x : ModularCurve.ModuliPoint N K) (v : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldFullC K N))
    (h : ModularCurve.IsModuliPlaceOf K N x v)
    (a : ↥(ModularCurve.modularFunctionFieldFullC K N)) (ha : (∃ P : Polynomial (Polynomial K), P.Monic ∧ Polynomial.eval₂ (Polynomial.aeval (R := K) (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N))).toRingHom a P = 0)) :
    a ∈ v.toValuationSubring := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsModuliPlaceOf_mem_toValuationSubring_of_isIntegral_jModElt.solution
