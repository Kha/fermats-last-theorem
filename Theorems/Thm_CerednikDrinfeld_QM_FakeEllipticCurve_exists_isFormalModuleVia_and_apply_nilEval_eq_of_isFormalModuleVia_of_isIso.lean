import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleVia_and_apply_nilEval_eq_of_isFormalModuleVia_of_isIso
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleVia_and_apply_nilEval_eq_of_isFormalModuleVia_of_isIso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q)
    (B : Type) [CommRing B] (E : FakeEllipticCurve Λ N B) (X Y : FormalODModule q B)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    (u : FormalODModule.Hom X Y) (hu : u.IsIso) :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates E.f 2, E.IsFormalModuleVia coord Y θ' ∧
      ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ' B' (fun i => MvFormalGroup.nilEval n (u.toSeries i) s) = θ B' s := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleVia_and_apply_nilEval_eq_of_isFormalModuleVia_of_isIso.solution
