import Mathlib
import Theorems.Thm_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType
import P2M.Util
namespace P2MW.S_Algebra_IsInvariant_flat_and_finiteType_of_isDedekindDomain

set_option autoImplicit false

theorem solution
    {B S A : Type*} [CommRing B] [IsDedekindDomain B] [CommRing S] [CommRing A]
    [Algebra B S] [Algebra B A] [Algebra S A] [IsScalarTower B S A] [FaithfulSMul S A]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G A] [Algebra.IsInvariant S A G]
    [Module.Flat B A] [Algebra.FiniteType B A] :
    Module.Flat B S ∧ Algebra.FiniteType B S := by
  haveI : Module.IsTorsionFree B A := Module.Flat.isTorsionFree
  have hinj : Function.Injective (IsScalarTower.toAlgHom B S A) := FaithfulSMul.algebraMap_injective S A
  haveI : Module.IsTorsionFree B S :=
    hinj.moduleIsTorsionFree _ (fun r s => map_smul (IsScalarTower.toAlgHom B S A) r s)
  exact ⟨inferInstance, (Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType B S A G).2⟩
