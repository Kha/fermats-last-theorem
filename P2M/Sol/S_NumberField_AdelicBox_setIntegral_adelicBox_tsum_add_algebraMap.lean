import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Mathlib
import P2M.Util
namespace P2MW.S_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain
open scoped ENNReal

noncomputable section

namespace M4aP3B
namespace Rows
namespace Unfold

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (F : Type) [Field F] [NumberField F]

scoped instance instNontrivialAdeleRing : Nontrivial (AdeleRing (𝓞 F) F) := by
  haveI : Inhabited (InfinitePlace F) := Classical.inhabited_of_nonempty inferInstance
  haveI : Nontrivial (InfiniteAdeleRing F) :=
    inferInstanceAs (Nontrivial ((w : InfinitePlace F) → w.Completion))
  exact inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

def principalEquiv : F ≃ AdeleRing.principalSubgroup (𝓞 F) F :=
  Equiv.ofBijective (fun k => ⟨algebraMap F (AdeleRing (𝓞 F) F) k, k, rfl⟩)
    ⟨fun a b h => (algebraMap F (AdeleRing (𝓞 F) F)).injective (congrArg Subtype.val h),
     by rintro ⟨_, k, rfl⟩; exact ⟨k, rfl⟩⟩

scoped instance instCountablePrincipal : Countable (AdeleRing.principalSubgroup (𝓞 F) F) :=
  (principalEquiv F).symm.injective.countable

theorem setIntegral_adelicBox_tsum_add_algebraMap_impl (Φ : AdeleRing (𝓞 F) F → ℂ)
    (hΦ : Integrable Φ (adelicAddHaar (𝓞 F) F)) :
    ∫ t in adelicBox F, (∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ))
        ∂(adelicAddHaar (𝓞 F) F)
      = ∫ t, Φ t ∂(adelicAddHaar (𝓞 F) F) := by
  have hFD := isAddFundamentalDomain_adelicBox_adelicAddHaar F
  have hre : ∀ t : AdeleRing (𝓞 F) F, (∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ))
      = ∑' g : AdeleRing.principalSubgroup (𝓞 F) F, Φ (g +ᵥ t) := by
    intro t
    rw [← (principalEquiv F).tsum_eq]
    refine tsum_congr fun ξ => ?_
    show Φ (t + algebraMap F _ ξ) = Φ (algebraMap F (AdeleRing (𝓞 F) F) ξ + t)
    rw [add_comm]
  simp_rw [hre]
  have hmeas : ∀ g : AdeleRing.principalSubgroup (𝓞 F) F,
      AEStronglyMeasurable (fun t => Φ (g +ᵥ t))
        ((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)) := fun g =>
    (hΦ.comp_add_left (g : AdeleRing (𝓞 F) F)).aestronglyMeasurable.restrict
  have hfin : ∑' g : AdeleRing.principalSubgroup (𝓞 F) F,
      ∫⁻ t in adelicBox F, ‖Φ (g +ᵥ t)‖ₑ ∂(adelicAddHaar (𝓞 F) F) ≠ ∞ := by
    rw [← hFD.lintegral_eq_tsum'' (fun t => ‖Φ t‖ₑ)]
    exact hΦ.2.ne
  rw [integral_tsum hmeas hfin]
  exact (hFD.integral_eq_tsum'' Φ hΦ).symm

end M4aP3B.Rows.Unfold
p2m_reactivate "P2MW.S_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap.M4aP3B P2MW.S_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap.M4aP3B.Rows P2MW.S_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap.M4aP3B.Rows.Unfold"
p2m_reactivate "P2MW.S_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap.M4aP3B P2MW.S_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap.M4aP3B.Rows"
p2m_reactivate "P2MW.S_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap.M4aP3B"

end
p2m_reactivate "P2MW.S_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap.M4aP3B P2MW.S_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap.M4aP3B.Rows P2MW.S_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap.M4aP3B.Rows.Unfold"


open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain

theorem solution (F : Type) [Field F]
    [NumberField F] (Φ : AdeleRing (𝓞 F) F → ℂ) (hΦ : Integrable Φ (adelicAddHaar (𝓞 F) F)) :
    ∫ t in adelicBox F, (∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ))
        ∂(adelicAddHaar (𝓞 F) F)
      = ∫ t, Φ t ∂(adelicAddHaar (𝓞 F) F) := by
  exact M4aP3B.Rows.Unfold.setIntegral_adelicBox_tsum_add_algebraMap_impl F Φ hΦ
