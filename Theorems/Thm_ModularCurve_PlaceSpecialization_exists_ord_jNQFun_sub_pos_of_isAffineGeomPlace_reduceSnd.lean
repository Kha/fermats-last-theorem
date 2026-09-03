import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (haff : IsAffineGeomPlace k N (P.reduceSnd Q)) :
    ∃ a : A, 0 < Q.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_refl (N * q)))⟩ : ↥(modularFunctionFieldBar (N * q))) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ∧
      0 < (P.reduceSnd Q).ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red a)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_exists_ord_jNQFun_sub_pos_of_isAffineGeomPlace_reduceSnd.solution
