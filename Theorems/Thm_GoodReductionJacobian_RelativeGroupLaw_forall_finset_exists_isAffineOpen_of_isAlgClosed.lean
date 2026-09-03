import Definitions.Def_JacJ1Iface
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_forall_finset_exists_isAffineOpen_of_isAlgClosed
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.forall_finset_exists_isAffineOpen_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    (hA : AbelianSchemePropertyBundle k f) :
    ∀ S : Finset A, ∃ U : A.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_finset_exists_isAffineOpen_of_isAlgClosed.solution
