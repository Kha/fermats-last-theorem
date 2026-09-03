import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_hom_isFormalCompletionAlong_of_isFormalModuleVia
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld
  CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_hom_isFormalCompletionAlong_of_isFormalModuleVia
    {q : ℕ} [Fact q.Prime]

    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (coord : ↥Λ → Zp2 q × Zp2 q)
    (hdense : ∀ (k : ℕ) (α β : Zp2 q), ∃ m : ↥Λ,
      (coord m).1 - α ∈ Ideal.span {((q : Zp2 q)) ^ k} ∧ (coord m).2 - β ∈ Ideal.span {((q : Zp2 q)) ^ k})
    {N : ℕ}

    {B : Type} [CommRing B] (hq : IsNilpotent (q : B))

    (E E' : FakeEllipticCurve Λ N B) (X X' : FormalODModule q B)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2)
    (hθ : E.IsFormalModuleVia coord X θ) (hθ' : E'.IsFormalModuleVia coord X' θ')

    (h : E.A ⟶ E'.A) (hh : h ≫ E'.f = E.f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t E.f),
      mapPt h hh (E.L.mul t P Q) = E'.L.mul t (mapPt h hh P) (mapPt h hh Q))
    (hlin : ∀ m : ↥Λ, E.act m ≫ h = h ≫ E'.act m) :
    ∃! u : X.Hom X', IsFormalCompletionAlong θ θ' h hh u.toSeries := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_hom_isFormalCompletionAlong_of_isFormalModuleVia.solution
