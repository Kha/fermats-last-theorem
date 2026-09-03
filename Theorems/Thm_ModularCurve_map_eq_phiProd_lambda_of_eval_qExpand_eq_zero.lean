import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_map_eq_phiProd_lambda_of_eval_qExpand_eq_zero
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.map_eq_phiProd_lambda_of_eval_qExpand_eq_zero
    {K : Type*} [Field K] [Algebra ℚ K] (q : ℕ) [Fact q.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) q)
    (P : Polynomial (LaurentSeries ℚ)) (hP : P.Monic) (hdeg : P.natDegree = q + 1)
    (h0 : P.eval (lambdaNModC ℚ q) = 0)
    (h1 : (P.map (qExpand ℚ q)).eval (lambdaModC ℚ) = 0) :
    P.map ((coeffEmb K).comp (qExpand ℚ q)) =
      phiProd q (Fin.cons (qExpand K (q * q) (lambdaModC K))
        (fun b : Fin q => qTwist (ζ ^ (b : ℕ)) (lambdaModC K)) : Fin (q + 1) → LaurentSeries K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_map_eq_phiProd_lambda_of_eval_qExpand_eq_zero.solution
