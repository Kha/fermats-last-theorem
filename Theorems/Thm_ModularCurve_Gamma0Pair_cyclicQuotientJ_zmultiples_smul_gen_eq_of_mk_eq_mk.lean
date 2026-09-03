import Mathlib
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import P2M.Util
import P2M.Sol.S_ModularCurve_Gamma0Pair_cyclicQuotientJ_zmultiples_smul_gen_eq_of_mk_eq_mk

set_option autoImplicit false

universe u

theorem ModularCurve.Gamma0Pair.cyclicQuotientJ_zmultiples_smul_gen_eq_of_mk_eq_mk
    {L : Type u} [Field L] [DecidableEq L] {N : ℕ} [NeZero N] (hN : (N : L) ≠ 0)
    (P Q : ModularCurve.Gamma0Pair N L)
    (h : (Quot.mk _ P : ModularCurve.ModuliPoint N L) = Quot.mk _ Q)
    (d : ℕ) (hd : d ∣ N) :
    P.toCurve.cyclicQuotientJ (AddSubgroup.zmultiples ((N / d) • P.gen)) d =
      Q.toCurve.cyclicQuotientJ (AddSubgroup.zmultiples ((N / d) • Q.gen)) d := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Gamma0Pair_cyclicQuotientJ_zmultiples_smul_gen_eq_of_mk_eq_mk.solution
