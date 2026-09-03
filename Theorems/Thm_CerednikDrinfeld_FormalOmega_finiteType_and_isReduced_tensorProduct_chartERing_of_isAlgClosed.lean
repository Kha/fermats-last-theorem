import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_finiteType_and_isReduced_tensorProduct_chartERing_of_isAlgClosed

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic TensorProduct

open CategoryTheory AlgebraicGeometry

theorem CerednikDrinfeld.FormalOmega.finiteType_and_isReduced_tensorProduct_chartERing_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    [Algebra ℤ_[p] (WittVector p k ⧸ CerednikDrinfeld.SpecialFormal.pIdeal p (WittVector p k))] :
    Algebra.FiniteType (WittVector p k ⧸ CerednikDrinfeld.SpecialFormal.pIdeal p (WittVector p k))
        ((WittVector p k ⧸ CerednikDrinfeld.SpecialFormal.pIdeal p (WittVector p k)) ⊗[ℤ_[p]]
          chartERing ℤ_[p] (p : ℤ_[p]) p) ∧
      IsReduced ((WittVector p k ⧸ CerednikDrinfeld.SpecialFormal.pIdeal p (WittVector p k)) ⊗[ℤ_[p]]
          chartERing ℤ_[p] (p : ℤ_[p]) p) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_finiteType_and_isReduced_tensorProduct_chartERing_of_isAlgClosed.solution
