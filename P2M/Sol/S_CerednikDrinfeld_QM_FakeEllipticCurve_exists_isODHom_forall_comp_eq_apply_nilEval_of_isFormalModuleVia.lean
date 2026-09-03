import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_hom_isFormalCompletionAlong_of_isFormalModuleVia
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isODHom_forall_comp_eq_apply_nilEval_of_isFormalModuleVia
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal

theorem solution
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    {L : Type} [CommRing L] [IsNoetherianRing L] (hLr : IsNilpotent ((r : ℕ) : L))
    (E E' : FakeEllipticCurve Λ N L) (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t E.f),
      mapPt q hq (E.L.mul t P Q) = E'.L.mul t (mapPt q hq P) (mapPt q hq Q))
    (hlin : ∀ x : ↥Λ, E.act x ≫ q = q ≫ E'.act x)
    (X : FormalODModule r L) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    (X' : FormalODModule r L) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2) (hX' : E'.IsFormalModuleVia coord X' θ') :
    ∃ qhat : Series L, FormalODModule.IsODHom X X' qhat ∧
      ∀ (B'' : Type) [CommRing B''] [Algebra L B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θ B'' s).1 ≫ q = (θ' B'' (fun i => MvFormalGroup.nilEval n (qhat i) s)).1 := by
  obtain ⟨u, hu, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_hom_isFormalCompletionAlong_of_isFormalModuleVia coord hcoord.dense hLr
      E E' X X' θ θ' hX hX' q hq hmul hlin
  refine ⟨u.toSeries, u.isODHom, ?_⟩
  intro B'' _ _ J n hJ s hs
  have h := congrArg Subtype.val (hu B'' J n hJ s hs)
  rw [mapPt_coe] at h
  exact h.symm
