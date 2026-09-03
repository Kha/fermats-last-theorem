import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_nonempty_basis_of_finrank_eq_pow
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.nonempty_basis_of_finrank_eq_pow
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}
    (Φ : MvFormalGroup d k) [Φ.IsComm] (h : ℕ)
    (hdeg : Module.finrank k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (Φ.nthSeries p))) = p ^ h) :
    Nonempty (Module.Basis (Fin h) (WittVector p k) (MvFormalGroup.CartierModule p Φ)) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_nonempty_basis_of_finrank_eq_pow.solution
