import Theorems.Thm_MvFormalGroup_Hom_eq_of_forall_subst_curve_eq
import Theorems.Thm_MvFormalGroup_CartierModule_subst_curve_eq_of_forall_map_eq_of_algebra_padicInt
import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import P2M.Util
namespace P2MW.S_MvFormalGroup_CartierModule_eq_of_forall_map_eq_of_algebra_padicInt
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R]
    [Algebra (PadicInt p) R]
    {d d' : ℕ} (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R) [Φ.IsComm] [Φ'.IsComm]
    (φ ψ : Φ.Hom Φ')
    (h : ∀ f : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.map φ f = MvFormalGroup.CartierModule.map ψ f) :
    φ = ψ := by
  exact MvFormalGroup.Hom.eq_of_forall_subst_curve_eq Φ Φ' φ ψ
    (fun γ hγ k => MvFormalGroup.CartierModule.subst_curve_eq_of_forall_map_eq_of_algebra_padicInt p Φ Φ' φ ψ h γ hγ k)
