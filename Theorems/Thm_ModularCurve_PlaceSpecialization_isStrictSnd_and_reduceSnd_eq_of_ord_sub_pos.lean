import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint
import Definitions.Def_MDivRepresents
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve
theorem ModularCurve.PlaceSpecialization.isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQ : P.IsStrictSnd Q)
    (hsm : ∃ c : k × k, IsCentreOf k N c (P.reduceSnd Q) ∧
      ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceSnd Q)
    (hgen : (P.reduceSnd Q).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jGeomGen k N) ∧
      (P.reduceSnd Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jNGeomGen k N))
    (a b c a' b' c' : A) (ha : red a' = red a) (hb : red b' = red b) (hc : red c' = red c)
    (haQ : 0 < Q.ord (PlaceSpecialization.ProlongationTuple.jQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)))
    (hbQ : 0 < Q.ord (PlaceSpecialization.jNQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ)))
    (hcQ : 0 < Q.ord (PlaceSpecialization.ProlongationTuple.jFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)))
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (haW : 0 < W.ord (PlaceSpecialization.ProlongationTuple.jQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a' : AlgebraicClosure ℚ)))
    (hbW : 0 < W.ord (PlaceSpecialization.jNQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b' : AlgebraicClosure ℚ)))
    (hcW : 0 < W.ord (PlaceSpecialization.ProlongationTuple.jFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c' : AlgebraicClosure ℚ))) :
    P.IsStrictSnd W ∧ P.reduceSnd W = P.reduceSnd Q := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos.solution
