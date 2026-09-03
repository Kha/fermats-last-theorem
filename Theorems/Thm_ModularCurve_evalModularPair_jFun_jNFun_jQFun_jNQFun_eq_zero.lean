import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_MDivRepresents
import P2M.Util
import P2M.Sol.S_ModularCurve_evalModularPair_jFun_jNFun_jQFun_jNQFun_eq_zero
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.evalModularPair_jFun_jNFun_jQFun_jNQFun_eq_zero
    (N q : ℕ) [NeZero N] [Fact q.Prime]
    (dataN : ModularPolynomialData N) (dataq : ModularPolynomialData q) :
    evalModularPair (PlaceSpecialization.ProlongationTuple.jFun N q) (PlaceSpecialization.jNFun N q) dataN.Φ = 0 ∧
    evalModularPair (PlaceSpecialization.ProlongationTuple.jQFun N q) (PlaceSpecialization.jNQFun N q) dataN.Φ = 0 ∧
    evalModularPair (PlaceSpecialization.ProlongationTuple.jFun N q) (PlaceSpecialization.ProlongationTuple.jQFun N q) dataq.Φ = 0 ∧
    evalModularPair (PlaceSpecialization.jNFun N q) (PlaceSpecialization.jNQFun N q) dataq.Φ = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_evalModularPair_jFun_jNFun_jQFun_jNQFun_eq_zero.solution
