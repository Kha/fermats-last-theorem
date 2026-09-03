import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_addMonoidHom_cartierModule_injective_of_isAlgClosed
attribute [-instance] MvFormalGroup.CartierModule.instModuleWittVector instTopologicallyFGOfFiniteType
attribute [-simp] MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.exists_addMonoidHom_cartierModule_injective_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ Φ' : CerednikDrinfeld.SpecialFormalODModule p j) :
    ∃ θ : MvFormalGroup.CartierModule p Φ.F →+ MvFormalGroup.CartierModule p Φ'.F,
      Function.Injective θ ∧
      (∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
        MvFormalGroup.CartierModule.frobenius (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.verschiebung f) =
        MvFormalGroup.CartierModule.verschiebung (θ f)) ∧
      (∀ (a : k) f, θ (MvFormalGroup.CartierModule.homothety a f) =
        MvFormalGroup.CartierModule.homothety a (θ f)) ∧
      (∀ (a : CerednikDrinfeld.Zp2 p) f,
        θ (MvFormalGroup.CartierModule.endAct (Φ.actEnd a) f) =
          MvFormalGroup.CartierModule.endAct (Φ'.actEnd a) (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.endAct Φ.varpiEnd f) =
        MvFormalGroup.CartierModule.endAct Φ'.varpiEnd (θ f)) ∧
      ∃ N : ℕ, ∀ g : MvFormalGroup.CartierModule p Φ'.F,
        ∃ f : MvFormalGroup.CartierModule p Φ.F, θ f = p ^ N • g := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_addMonoidHom_cartierModule_injective_of_isAlgClosed.solution
