import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_map_injective_of_finite_quotient

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.map_injective_of_finite_quotient
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] {d d' : ℕ}
    (Φ : MvFormalGroup d k) [Φ.IsComm] (Φ' : MvFormalGroup d' k) [Φ'.IsComm] (φ : Φ.Hom Φ')
    (hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range φ.toPowerSeries))) :
    Function.Injective (MvFormalGroup.CartierModule.map (p := p) φ) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_map_injective_of_finite_quotient.solution
