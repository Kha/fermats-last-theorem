import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_unit_zero_eq_one_of_bijective
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_cechFinrank_unit_zero_eq_one
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace P2mH0AV

variable {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (.of K))

theorem geometricallyConnected_of_geometricallyIrreducible [GeometricallyIrreducible f] :
    GeometricallyConnected f := by
  rw [GeometricallyConnected.eq_geometrically]
  have h := (GeometricallyIrreducible.eq_geometrically ▸ ‹GeometricallyIrreducible f› :
    geometrically (fun X => IrreducibleSpace X) f)
  intro L _ y Y p q hpq
  haveI : IrreducibleSpace Y := h y p q hpq
  infer_instance

theorem bijective_algebraMap_of_bijective_appTop (h : Function.Bijective f.appTop) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
    Function.Bijective (algebraMap K Γ(A, ⊤)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
  have e : (algebraMap K Γ(A, ⊤) : K → Γ(A, ⊤)) =
      (A.presheaf.map (homOfLE (le_top : (⊤ : A.Opens) ≤ f ⁻¹ᵁ ⊤)).op).hom ∘ f.appTop.hom ∘
        (Scheme.ΓSpecIso (.of K)).inv.hom := by
    funext r
    rfl
  rw [e]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp h ?_)
  · have : homOfLE (le_top : (⊤ : A.Opens) ≤ f ⁻¹ᵁ ⊤) = 𝟙 _ := Subsingleton.elim _ _
    rw [this, op_id, A.presheaf.map_id]
    exact Function.bijective_id
  · exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv)

theorem main (hA : GoodReductionJacobian.AbelianSchemePropertyBundle K f) (𝒦 : A.OrderedAffineCover) :
    (OModulePresheaf.unit f).cechFinrank 𝒦 0 = 1 := by
  haveI : IsProper f := hA.proper
  haveI : GeometricallyIntegral f := hA.geometricallyIntegral
  haveI : GeometricallyConnected f := geometricallyConnected_of_geometricallyIrreducible f
  have hΓ := AlgebraicGeometry.bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected f
  exact AlgebraicGeometry.OModulePresheaf.cechFinrank_unit_zero_eq_one_of_bijective f
    (bijective_algebraMap_of_bijective_appTop f hΓ) 𝒦

end P2mH0AV

theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle K f) (𝒦 : A.OrderedAffineCover) :
    (OModulePresheaf.unit f).cechFinrank 𝒦 0 = 1 :=
  P2mH0AV.main f hA 𝒦
