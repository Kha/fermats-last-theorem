import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_locallyQuasiFinite_of_field
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_locallyQuasiFinite_of_field
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    [Smooth f] [PreconnectedSpace A]
    (G : RelativeGroupLaw k f) (n : ℕ) [LocallyQuasiFinite (G.schemeNsmul n)] :
    Flat (G.schemeNsmul n) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_locallyQuasiFinite_of_field.solution
