import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_linearMap_bijOn_gradedPiece_apply_eq_of_bijective_invariants_of_isCritical_of_isAlgClosed
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.exists_linearMap_bijOn_gradedPiece_apply_eq_of_bijective_invariants_of_isCritical_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (j : Zp2 p →+* K)
    (X X' : FormalODModule p K) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hX' : X'.IsSpecial j) (hX'4 : X'.HasHeight 4)
    (i : ℕ) (hi : FormalODModule.CritChart.IsCritical X j i) (hi' : FormalODModule.CritChart.IsCritical X' j i)
    (θ₀ : FormalODModule.CritChart.invariants X j i →+ FormalODModule.CritChart.invariants X' j i)
    (hθ₀ : Function.Bijective θ₀) :
    ∃ Θ : MvFormalGroup.CartierModule p X.F →ₗ[WittVector p K] MvFormalGroup.CartierModule p X'.F,
      Set.BijOn Θ (X.gradedPiece j i : Set (MvFormalGroup.CartierModule p X.F)) (X'.gradedPiece j i) ∧
      ∀ m : FormalODModule.CritChart.invariants X j i,
        Θ (m : MvFormalGroup.CartierModule p X.F) = ((θ₀ m : FormalODModule.CritChart.invariants X' j i) : MvFormalGroup.CartierModule p X'.F) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_linearMap_bijOn_gradedPiece_apply_eq_of_bijective_invariants_of_isCritical_of_isAlgClosed.solution
