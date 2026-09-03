import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (j₀ : A)
    (hQ : 0 < Q.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (j₀ : AlgebraicClosure ℚ))) :
    0 < (P.reduceFst Q).ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red j₀)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos.solution
