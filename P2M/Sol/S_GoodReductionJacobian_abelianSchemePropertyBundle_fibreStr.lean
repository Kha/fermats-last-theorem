import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    AbelianSchemePropertyBundle (RelativeGroupLaw.baseResidueField s) (RelativeGroupLaw.fibreStr f s) := by
  haveI : Smooth f := hA.smooth
  haveI : IsProper f := hA.proper
  refine ⟨inferInstance, inferInstance, ?_, ⟨(Classical.choice hA.hasGroupLaw).fibre s⟩⟩
  intro s'

  have huniv : (RelativeGroupLaw.fibreStr f s).base ⁻¹' {s'} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [huniv]

  have hconn : _root_.IsConnected (f.base ⁻¹' {s}) := hA.connectedFibres s
  haveI : ConnectedSpace (f.base ⁻¹' {s}) := isConnected_iff_connectedSpace.mp hconn
  have h1 : _root_.IsConnected (Set.univ : Set (f.fiber s)) := by
    have h := (isConnected_univ (α := f.base ⁻¹' {s})).image _ (f.fiberHomeo s).symm.continuous.continuousOn
    rwa [Set.image_univ_of_surjective (f.fiberHomeo s).symm.surjective] at h
  exact h1
