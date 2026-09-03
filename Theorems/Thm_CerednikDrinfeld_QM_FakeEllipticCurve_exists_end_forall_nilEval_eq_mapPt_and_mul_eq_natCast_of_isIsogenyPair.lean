import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_end_forall_nilEval_eq_mapPt_and_mul_eq_natCast_of_isIsogenyPair
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_end_forall_nilEval_eq_mapPt_and_mul_eq_natCast_of_isIsogenyPair
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k₀ : Type} [CommRing k₀]
    (A₀ : FakeEllipticCurve Λ N k₀) (coord : ↥Λ → Zp2 r × Zp2 r) (X₀ : FormalODModule r k₀)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (n : ℕ) (hn : (((n : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (e e' : A₀.A ⟶ A₀.A) (hee' : FakeEllipticCurve.IsIsogenyPair n A₀ A₀ e e')
    (he : e ≫ A₀.f = A₀.f) (he' : e' ≫ A₀.f = A₀.f)
    (ε : MvFormalGroup.End X₀.F)
    (hε : ∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ₀ B' (fun i => MvFormalGroup.nilEval m (ε.toPowerSeries i) s) = mapPt e he (θ₀ B' s)) :
    ∃ ε' : MvFormalGroup.End X₀.F,
      (∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ₀ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s) = mapPt e' he' (θ₀ B' s)) ∧
      ∀ δ : MvFormalGroup.End X₀.F,
        (∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
          ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
            θ₀ B' (fun i => MvFormalGroup.nilEval m (δ.toPowerSeries i) s) =
              mapPt (A₀.act ⟨((n : ℕ) : ℚ), hn⟩) (A₀.act_over _) (θ₀ B' s)) →
        ε' * ε = δ ∧ ε * ε' = δ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_end_forall_nilEval_eq_mapPt_and_mul_eq_natCast_of_isIsogenyPair.solution
