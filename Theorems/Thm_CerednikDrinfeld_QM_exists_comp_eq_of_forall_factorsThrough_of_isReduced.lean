import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced
    (k : Type u) [Field k] [IsAlgClosed k] {Z A C : Scheme.{u}}
    (g : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] [IsReduced Z]
    (f : A ⟶ Spec (CommRingCat.of k)) (i : C ⟶ A) [IsClosedImmersion i]
    (φ : Z ⟶ A) (hφ : φ ≫ f = g)
    (h : ∀ z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g, FactorsThrough i (mapPt φ hφ z)) :
    ∃ φ₀ : Z ⟶ C, φ₀ ≫ i = φ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced.solution
