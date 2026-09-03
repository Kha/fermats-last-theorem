import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_exists_add_eq_and_nonempty_basis_quotient_span_frobenius_of_finrank_eq_pow
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.exists_add_eq_and_nonempty_basis_quotient_span_frobenius_of_finrank_eq_pow
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}
    (Φ : MvFormalGroup d k) [Φ.IsComm] (h : ℕ)
    (hdeg : Module.finrank k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (Φ.nthSeries p))) = p ^ h) :
    ∃ e : ℕ, d + e = h ∧
      Nonempty (Module.Basis (Fin e) (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
        ((MvFormalGroup.CartierModule p Φ ⧸
            (Ideal.span {(p : WittVector p k)} • ⊤ :
              Submodule (WittVector p k) (MvFormalGroup.CartierModule p Φ))) ⧸
          Submodule.span (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
            (Set.range fun f : MvFormalGroup.CartierModule p Φ =>
              (Submodule.Quotient.mk (MvFormalGroup.CartierModule.frobenius f) :
                MvFormalGroup.CartierModule p Φ ⧸
                  (Ideal.span {(p : WittVector p k)} • ⊤ :
                    Submodule (WittVector p k) (MvFormalGroup.CartierModule p Φ)))))) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_exists_add_eq_and_nonempty_basis_quotient_span_frobenius_of_finrank_eq_pow.solution
