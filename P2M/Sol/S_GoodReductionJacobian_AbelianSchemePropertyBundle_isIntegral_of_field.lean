import Mathlib
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import Theorems.Thm_IsRegularLocalRing_isDomain
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

theorem solution {k : Type u} [Field k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)}
    (hJ : AbelianSchemePropertyBundle k f) : IsIntegral J := by
  haveI := hJ.smooth
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  haveI : IsLocallyNoetherian J := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : ConnectedSpace J := by
    rw [connectedSpace_iff_univ]
    have hc := hJ.connectedFibres default
    have heq : f.base ⁻¹' {(default : Spec (CommRingCat.of k))} = Set.univ := by
      ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rwa [heq] at hc
  exact AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk J
    fun x => by
      haveI := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) x
      exact IsRegularLocalRing.isDomain _
