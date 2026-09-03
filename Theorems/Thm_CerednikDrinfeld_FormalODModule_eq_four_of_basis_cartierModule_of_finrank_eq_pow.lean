import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_eq_four_of_basis_cartierModule_of_finrank_eq_pow
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u
theorem CerednikDrinfeld.FormalODModule.eq_four_of_basis_cartierModule_of_finrank_eq_pow
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p]
    (X : CerednikDrinfeld.FormalODModule p k)
    (b : Module.Basis (Fin 4) (WittVector p k) (MvFormalGroup.CartierModule p X.F))
    (h : ℕ)
    (hdeg : Module.finrank k
      (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (X.F.nthSeries p))) = p ^ h) :
    h = 4 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_eq_four_of_basis_cartierModule_of_finrank_eq_pow.solution
