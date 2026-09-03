import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_QAdicPlace
import P2M.Util
import P2M.Sol.S_ModularCurve_frobOnPlacesGeomLevel_qInftyPlaceBar

open ModularCurve AlgebraicCurve

theorem ModularCurve.frobOnPlacesGeomLevel_qInftyPlaceBar (k : Type*) [Field k] (N : ℕ) [NeZero N]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (h : ∃ j : modularFunctionFieldC k N, (qSeriesBar k (modularFunctionFieldC k N) j).order = -1) :
    frobOnPlacesGeomLevel k N data hKr (qInftyPlaceBar k (modularFunctionFieldC k N) h)
      = qInftyPlaceBar k (modularFunctionFieldC k N) h := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frobOnPlacesGeomLevel_qInftyPlaceBar.solution
