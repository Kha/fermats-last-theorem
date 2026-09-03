import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_isSupersingularPlace_of_forall_mem_iff_of_coe_eq_qExpand

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.isSupersingularPlace_of_forall_mem_iff_of_coe_eq_qExpand
    (q : ℕ) [Fact q.Prime] (N : ℕ) [NeZero N] (K : Type*) [Field K] [DecidableEq K] [CharP K q]
    (e : ℕ) (φ : ↥(modularFunctionFieldC K N) →+* ↥(modularFunctionFieldC K N))
    (hφ : ∀ g : ↥(modularFunctionFieldC K N),
      ((φ g : ↥(modularFunctionFieldC K N)) : LaurentSeries K) = qExpand K (q ^ e) (g : LaurentSeries K))
    (s s' : Place K ↥(modularFunctionFieldC K N))
    (h : ∀ g : ↥(modularFunctionFieldC K N), g ∈ s.toValuationSubring ↔ φ g ∈ s'.toValuationSubring)
    (hs' : s'.IsRational) (hs : IsSupersingularPlace q N K s) :
    IsSupersingularPlace q N K s' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isSupersingularPlace_of_forall_mem_iff_of_coe_eq_qExpand.solution
