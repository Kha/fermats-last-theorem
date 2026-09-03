import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.tangent_surjective_of_algebra_padicInt
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra ℤ_[p] R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Surjective
      (MvFormalGroup.CartierModule.tangent : MvFormalGroup.CartierModule p Φ → Fin d → R) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt.solution
