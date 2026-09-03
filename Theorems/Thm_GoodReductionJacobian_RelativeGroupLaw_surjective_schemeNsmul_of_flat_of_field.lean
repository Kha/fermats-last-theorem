import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.surjective_schemeNsmul_of_flat_of_field
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [IrreducibleSpace A]
    (G : RelativeGroupLaw k f)
    (hc : G.IsCommutative)
    (n : ℕ) [Flat (G.schemeNsmul n)] :
    Surjective (G.schemeNsmul n) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field.solution
