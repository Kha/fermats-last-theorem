import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_eq_mul_of_ne_zero
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_endDegree_inv_idPoint_eq_one_and_inv_eq_schemeHomOverComp_inv_idPoint
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace DegInvSol

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} (L : RelativeGroupLaw K f)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (t' : T' ⟶ Spec (CommRingCat.of K))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h1 : L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x)) (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      L.one t' := by
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural]
  have : (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) : SchemeHomOver t' f) *
      GoodReductionJacobian.schemeHomOverComp ψ hψ x = 1 := h1
  exact eq_inv_of_mul_eq_one_left this

theorem comp_inv_idPoint (hc : L.IsCommutative) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f) :
    letI := L.pointCommGroup hc f
    letI := L.pointCommGroup hc t
    NeronModelInfra.schemeHomOverComp x (RelativeGroupLaw.idPoint : SchemeHomOver f f)⁻¹ = x⁻¹ := by
  letI := L.pointCommGroup hc f
  letI := L.pointCommGroup hc t
  show NeronModelInfra.schemeHomOverComp x (L.inv f RelativeGroupLaw.idPoint) = L.inv t x
  have h := inv_natural L f t x.1 x.2 RelativeGroupLaw.idPoint
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint : SchemeHomOver f f) = x := by
    apply Subtype.ext; rw [GoodReductionJacobian.schemeHomOverComp_coe]; exact Category.comp_id _
  rw [hx] at h
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, ← GoodReductionJacobian.schemeHomOverComp_coe x.1 x.2, h]

theorem inv_idPoint_comp_self (hc : L.IsCommutative) :
    letI := L.pointCommGroup hc f
    ((RelativeGroupLaw.idPoint : SchemeHomOver f f)⁻¹).1 ≫ ((RelativeGroupLaw.idPoint : SchemeHomOver f f)⁻¹).1 = 𝟙 A := by
  letI := L.pointCommGroup hc f
  have h := comp_inv_idPoint L hc f ((RelativeGroupLaw.idPoint : SchemeHomOver f f)⁻¹)
  rw [inv_inv] at h
  have := congrArg Subtype.val h
  rw [NeronModelInfra.schemeHomOverComp_coe] at this
  exact this

end DegInvSol

open DegInvSol in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] :
    letI := L.pointCommGroup hc f
    L.endDegree (RelativeGroupLaw.idPoint : SchemeHomOver f f)⁻¹ = 1 ∧
      (∀ β : SchemeHomOver f f,
        β⁻¹ = NeronModelInfra.schemeHomOverComp β (RelativeGroupLaw.idPoint : SchemeHomOver f f)⁻¹) ∧
      ∀ (β : SchemeHomOver f f),
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
          NeronModelInfra.schemeHomOverComp (L.mul t x y) β =
            L.mul t (NeronModelInfra.schemeHomOverComp x β) (NeronModelInfra.schemeHomOverComp y β)) →
        L.endDegree β ≠ 0 →
        L.endDegree (NeronModelInfra.schemeHomOverComp β (RelativeGroupLaw.idPoint : SchemeHomOver f f)⁻¹) = L.endDegree β := by
  letI := L.pointCommGroup hc f

  let ν : SchemeHomOver f f := (RelativeGroupLaw.idPoint : SchemeHomOver f f)⁻¹
  haveI hiso : IsIso ν.1 := ⟨⟨ν.1, inv_idPoint_comp_self L hc, inv_idPoint_comp_self L hc⟩⟩
  haveI : IsIso (L.endKerStr ν) := by
    show IsIso (pullback.snd ν.1 (L.one (𝟙 (Spec (CommRingCat.of K)))).1)
    infer_instance
  haveI : IsFinite (L.endKerStr ν) := inferInstance
  have hdeg : L.endDegree ν = 1 := by
    rw [RelativeGroupLaw.endDegree_of_isFinite]
    exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _

  have hνhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) ν =
        L.mul t (NeronModelInfra.schemeHomOverComp x ν) (NeronModelInfra.schemeHomOverComp y ν) := by
    intro T t x y
    letI := L.pointCommGroup hc t
    rw [comp_inv_idPoint L hc t, comp_inv_idPoint L hc t, comp_inv_idPoint L hc t]
    exact mul_inv (x : SchemeHomOver t f) y
  refine ⟨hdeg, fun β => (comp_inv_idPoint L hc f β).symm, ?_⟩
  intro β hβ hβ0
  rw [GoodReductionJacobian.RelativeGroupLaw.endDegree_schemeHomOverComp_eq_mul_of_ne_zero K f L hc hA g β ν hβ hνhom hβ0
    (by rw [hdeg]; exact one_ne_zero), hdeg, mul_one]
