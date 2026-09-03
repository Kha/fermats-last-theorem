import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_nsmulPt_eq_one_of_forall_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.eq_of_nsmulPt_eq_one_of_forall_comp_eq
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) [IsFinite (L.schemeKerStr n)] [Etale (L.schemeKerStr n)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f)
    (hP : nsmulPt L t n P = L.one t) (hQ : nsmulPt L t n Q = L.one t)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (τ : Spec (CommRingCat.of k) ⟶ T), τ ≫ P.1 = τ ≫ Q.1) :
    P = Q := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_nsmulPt_eq_one_of_forall_comp_eq.solution
