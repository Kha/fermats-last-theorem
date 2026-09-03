import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import P2M.Util
import P2M.Sol.S_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve
theorem ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel
    (ℓ : ℕ) (K : Type*) [Field K] [Fact ℓ.Prime] [CharP K ℓ] [PerfectField K]
    (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData ℓ) (hKr : ModularCurve.KroneckerCongruence ℓ data)
    (w : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldC K N)) :
    ModularCurve.arithFrobC ℓ K N • w = ModularCurve.frobOnPlacesGeomLevel K N data hKr w := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel.solution
