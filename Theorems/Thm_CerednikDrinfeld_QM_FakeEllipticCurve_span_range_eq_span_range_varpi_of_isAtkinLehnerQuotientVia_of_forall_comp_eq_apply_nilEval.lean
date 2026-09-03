import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_span_range_eq_span_range_varpi_of_isAtkinLehnerQuotientVia_of_forall_comp_eq_apply_nilEval
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.span_range_eq_span_range_varpi_of_isAtkinLehnerQuotientVia_of_forall_comp_eq_apply_nilEval
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (hΛ : QuaternionAlgebra.IsOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    {L : Type} [CommRing L] [IsNoetherianRing L] (hLr : IsNilpotent ((r : ℕ) : L))
    (E E' : FakeEllipticCurve Λ N L)
    (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f) (q' : E'.A ⟶ E.A) (hq' : q' ≫ E.f = E'.f)
    (hAL : FakeEllipticCurve.IsAtkinLehnerQuotientVia r E E' q hq q' hq')
    (X : FormalODModule r L) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    (X' : FormalODModule r L) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2) (hX' : E'.IsFormalModuleVia coord X' θ')
    (qhat : Series L) (hq0 : ∀ i, MvPowerSeries.constantCoeff (qhat i) = 0)
    (hrep : ∀ (B'' : Type) [CommRing B''] [Algebra L B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θ B'' s).1 ≫ q = (θ' B'' (fun i => MvFormalGroup.nilEval n (qhat i) s)).1) :
    Ideal.span (Set.range qhat) = Ideal.span (Set.range X.varpi) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_span_range_eq_span_range_varpi_of_isAtkinLehnerQuotientVia_of_forall_comp_eq_apply_nilEval.solution
