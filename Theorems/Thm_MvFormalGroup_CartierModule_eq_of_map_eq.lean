import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_eq_of_map_eq
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.eq_of_map_eq
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d d' : ℕ}
    (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R) [Φ.IsComm] [Φ'.IsComm]
    (φ ψ : Φ.Hom Φ')
    (h : ∀ f : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.map φ f = MvFormalGroup.CartierModule.map ψ f) :
    φ = ψ := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_eq_of_map_eq.solution
