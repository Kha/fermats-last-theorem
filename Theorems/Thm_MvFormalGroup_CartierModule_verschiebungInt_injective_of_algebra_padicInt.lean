import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_verschiebungInt_injective_of_algebra_padicInt
attribute [-instance] MvFormalGroup.instIsCommMapRingHom
attribute [-simp] MvFormalGroup.CartierModule.toPowerSeries_baseChangeEqFun MvFormalGroup.toPowerSeries_map_ringHom MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.verschiebungInt_injective_of_algebra_padicInt
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra ℤ_[p] R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Injective (MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_verschiebungInt_injective_of_algebra_padicInt.solution
