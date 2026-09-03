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
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_forall_not_hasStructureConstants_add_ite_smul_eps_of_forall_ne_add_smul
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.forall_not_hasStructureConstants_add_ite_smul_eps_of_forall_ne_add_smul
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.toFormalODModule.IsHomogeneousVBasis j₀ γ)
    (a : ℕ → Fin 2 → k) (ha : X₀.toFormalODModule.HasStructureConstants γ a) (h01 : a 0 0 * a 0 1 = (q : k))
    (i₀ : Fin 2) (ha0 : a 0 i₀ = 0) (hu : a 0 (FormalODModule.piIndex 0 i₀) ≠ 0)
    (δ : Fin 3 → k)
    (hδ : ∀ v s : k, δ ≠ v • ![a 0 (FormalODModule.piIndex 0 i₀), -(a 0 (FormalODModule.piIndex 0 i₀) ^ q), -(a 1 i₀ ^ q)] +
        s • ![-(a 1 i₀), -(a 1 (FormalODModule.piIndex 0 i₀)), -(a 2 i₀)]) :
    ∀ (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F),
      (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis
          ((algebraMap k (DualNumber k)).comp j₀) γ' →
      ¬ (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).HasStructureConstants γ'
          (fun m i => algebraMap k (DualNumber k) (a m i) +
            (if m = 1 ∧ i = i₀ then δ 0 else if m = 1 ∧ i = FormalODModule.piIndex 0 i₀ then δ 1
              else if m = 2 ∧ i = i₀ then δ 2 else 0) • DualNumber.eps) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_forall_not_hasStructureConstants_add_ite_smul_eps_of_forall_ne_add_smul.solution
