import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_nsmulPt_eq_one_of_comp_eq_of_isNilpotent_ker
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.eq_of_nsmulPt_eq_one_of_comp_eq_of_isNilpotent_ker
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type u} [CommRing S] [IsLocalRing S] (E : FakeEllipticCurve Λ N S)
    (m : ℕ) (hm : IsUnit ((m : ℕ) : S))
    {T T₀ : Scheme.{u}} (i : T₀ ⟶ T) [IsClosedImmersion i] (hi : IsNilpotent i.ker)
    (t : T ⟶ Spec (CommRingCat.of S)) (P P' : SchemeHomOver t E.f)
    (hP : nsmulPt E.L t m P = E.L.one t) (hP' : nsmulPt E.L t m P' = E.L.one t)
    (h : i ≫ P.1 = i ≫ P'.1) :
    P = P' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_nsmulPt_eq_one_of_comp_eq_of_isNilpotent_ker.solution
