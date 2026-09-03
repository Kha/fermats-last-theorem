import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentAction
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.DescentAction.effective_of_finiteEtale
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {X' : Scheme.{u}} {x' : X' ⟶ Spec (CommRingCat.of R')}
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) x')
    (haff : ∀ S : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    A.Effective := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale.solution
