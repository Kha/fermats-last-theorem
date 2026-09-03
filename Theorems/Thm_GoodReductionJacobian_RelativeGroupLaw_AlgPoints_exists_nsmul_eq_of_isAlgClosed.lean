import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_AlgPoints_exists_nsmul_eq_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.AlgPoints.exists_nsmul_eq_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (n : ℕ) (hn : (n : k) ≠ 0) (y : L.AlgPoints hc k) :
    ∃ y₁ : L.AlgPoints hc k, n • y₁ = y := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_AlgPoints_exists_nsmul_eq_of_isAlgClosed.solution
