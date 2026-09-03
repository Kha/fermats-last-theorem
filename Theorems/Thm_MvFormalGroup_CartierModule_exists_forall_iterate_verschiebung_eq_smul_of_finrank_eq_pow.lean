import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_exists_forall_iterate_verschiebung_eq_smul_of_finrank_eq_pow
attribute [-instance] MvFormalGroup.instIsCommMapRingHom instTopologicallyFGOfFiniteType
attribute [-simp] MvFormalGroup.CartierModule.toPowerSeries_baseChangeEqFun MvFormalGroup.toPowerSeries_map_ringHom MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.exists_forall_iterate_verschiebung_eq_smul_of_finrank_eq_pow
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}
    (Φ : MvFormalGroup d k) [Φ.IsComm] (h : ℕ)
    (hdeg : Module.finrank k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (Φ.nthSeries p))) = p ^ h) :
    ∃ N : ℕ, ∀ f : MvFormalGroup.CartierModule p Φ, ∃ g : MvFormalGroup.CartierModule p Φ,
      (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[N] f =
        (p : WittVector p k) • g := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_exists_forall_iterate_verschiebung_eq_smul_of_finrank_eq_pow.solution
