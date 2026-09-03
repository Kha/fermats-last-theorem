import Mathlib
import Definitions.Def_JacJ1Iface
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle
    {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k))
    [Smooth g] [IsSeparated g] [QuasiCompact g] [IrreducibleSpace X]
    {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of k)} (hA : AbelianSchemePropertyBundle k fA)
    {U : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u] [Nonempty U]
    (φ : U ⟶ A) (hφ : φ ≫ fA = u ≫ g) :
    ∃ ψ : X ⟶ A, ψ ≫ fA = g ∧ u ≫ ψ = φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.solution
