import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_isAtkinLehnerQuotientVia_comp_eq_of_preservesLevel
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_of_isAtkinLehnerQuotientVia_comp_eq_of_preservesLevel
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrbarN : ¬ rbar ∣ N)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharP k₀ r] (A₀ A₀w : FakeEllipticCurve Λ N k₀)
    (aw : A₀.A ⟶ A₀w.A) (haw : aw ≫ A₀w.f = A₀.f) (aw' : A₀w.A ⟶ A₀.A) (haw' : aw' ≫ A₀.f = A₀w.f)
    (hAL : FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar A₀ A₀w aw haw aw' haw')
    (f : A₀.A ⟶ A₀.A) (hf : f ≫ A₀.f = A₀.f) (hf_lev : FakeEllipticCurve.PreservesLevel A₀ A₀ f hf)
    (bw : A₀w.A ⟶ A₀.A) (hbw : bw ≫ A₀.f = A₀w.f)
    (hbw_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀w.f),
      mapPt bw hbw (A₀w.L.mul t P Q) = A₀.L.mul t (mapPt bw hbw P) (mapPt bw hbw Q))
    (hcomp : aw ≫ bw = f) :
    FakeEllipticCurve.PreservesLevel A₀w A₀ bw hbw := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_isAtkinLehnerQuotientVia_comp_eq_of_preservesLevel.solution
