import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    [QuasiCompact f'] [IsSeparated f'] :
    QuasiCompact f ∧ IsSeparated f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat.solution
