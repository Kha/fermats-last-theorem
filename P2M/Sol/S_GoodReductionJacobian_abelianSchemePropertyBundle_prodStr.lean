import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_abelianSchemePropertyBundle_prodStr
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {K : Type u} [Field K] {B C : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of K)}
    {h : C ⟶ Spec (CommRingCat.of K)} (hB : AbelianSchemePropertyBundle K g)
    (hC : AbelianSchemePropertyBundle K h) :
    AbelianSchemePropertyBundle K (prodStr g h) := by
  haveI : Smooth g := hB.smooth
  haveI : Smooth h := hC.smooth
  haveI : IsProper g := hB.proper
  haveI : IsProper h := hC.proper
  haveI : GeometricallyIntegral g := hB.geometricallyIntegral
  haveI : GeometricallyIntegral h := hC.geometricallyIntegral
  haveI : IrreducibleSpace C := GeometricallyIrreducible.irreducibleSpace_of_subsingleton h
  haveI : UniversallyOpen g := UniversallyOpen.of_flat g
  haveI : IrreducibleSpace ↥(pullback g h) := inferInstance
  obtain ⟨GB⟩ := hB.hasGroupLaw
  obtain ⟨GC⟩ := hC.hasGroupLaw
  refine ⟨inferInstance, inferInstance, fun s => ?_, ⟨GB.prod GC⟩⟩
  have hs : (prodStr g h).base ⁻¹' {s} = Set.univ :=
    Set.eq_univ_of_forall fun a => Subsingleton.elim _ _
  rw [hs, ← connectedSpace_iff_univ]
  infer_instance
