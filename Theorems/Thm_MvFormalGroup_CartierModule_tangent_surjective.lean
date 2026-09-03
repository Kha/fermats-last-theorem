import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_tangent_surjective
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.tangent_surjective
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Surjective
      (MvFormalGroup.CartierModule.tangent : MvFormalGroup.CartierModule p Φ → Fin d → R) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_tangent_surjective.solution
