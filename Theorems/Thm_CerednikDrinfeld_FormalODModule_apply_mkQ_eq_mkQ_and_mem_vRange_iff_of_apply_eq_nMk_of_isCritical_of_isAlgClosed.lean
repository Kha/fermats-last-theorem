import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_apply_mkQ_eq_mkQ_and_mem_vRange_iff_of_apply_eq_nMk_of_isCritical_of_isAlgClosed
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.apply_mkQ_eq_mkQ_and_mem_vRange_iff_of_apply_eq_nMk_of_isCritical_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (j : Zp2 p →+* K)
    (X X' : FormalODModule p K) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hX' : X'.IsSpecial j) (hX'4 : X'.HasHeight 4)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) (hc' : IsCompl (X'.gradedPiece j 0) (X'.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod) (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (L' : (X'.toGradedCartierModuleData j hc').M →+ (X'.toGradedCartierModuleData j hc').NMod) (hL' : (X'.toGradedCartierModuleData j hc').IsCanonicalLMap L')
    (i : Fin 2)
    (hi : ∀ m ∈ X.gradedPiece j (i : ℕ), ∃ y : MvFormalGroup.CartierModule p X.F,
      MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct X.varpiEnd m)
    (θη : (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i →+ (X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)
    (τ : (X.toGradedCartierModuleData j hc).LieQuot →ₗ[WittVector p K] (X'.toGradedCartierModuleData j hc').LieQuot) (hτ : Function.Injective τ)
    (hcompat : ∀ (m : (X.toGradedCartierModuleData j hc).M) (m' : (X'.toGradedCartierModuleData j hc').M) (hm : (X.toGradedCartierModuleData j hc).nMk (m, 0) ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
      ((θη ⟨(X.toGradedCartierModuleData j hc).nMk (m, 0), hm⟩ : (X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : (X'.toGradedCartierModuleData j hc').NMod) = (X'.toGradedCartierModuleData j hc').nMk (m', 0) →
        τ ((X.toGradedCartierModuleData j hc).vRange.mkQ m) = (X'.toGradedCartierModuleData j hc').vRange.mkQ m')
    (Θ : MvFormalGroup.CartierModule p X.F →ₗ[WittVector p K] MvFormalGroup.CartierModule p X'.F)
    (hΘ : ∀ (m : (X.toGradedCartierModuleData j hc).M) (hm : (X.toGradedCartierModuleData j hc).nMk (m, 0) ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
      ((θη ⟨(X.toGradedCartierModuleData j hc).nMk (m, 0), hm⟩ : (X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : (X'.toGradedCartierModuleData j hc').NMod) = (X'.toGradedCartierModuleData j hc').nMk (Θ m, 0)) :
    ∀ x ∈ X.gradedPiece j (i : ℕ),
      τ ((X.toGradedCartierModuleData j hc).vRange.mkQ x) = (X'.toGradedCartierModuleData j hc').vRange.mkQ (Θ x) ∧
      ((∃ y : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt y = x) ↔
        (∃ y' : MvFormalGroup.CartierModule p X'.F, MvFormalGroup.CartierModule.verschiebungInt y' = Θ x)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_apply_mkQ_eq_mkQ_and_mem_vRange_iff_of_apply_eq_nMk_of_isCritical_of_isAlgClosed.solution
