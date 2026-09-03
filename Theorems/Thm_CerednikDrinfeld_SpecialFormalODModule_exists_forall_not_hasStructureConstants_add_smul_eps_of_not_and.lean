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
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)))
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.toFormalODModule.IsHomogeneousVBasis j₀ γ)
    (a : ℕ → Fin 2 → k) (ha : X₀.toFormalODModule.HasStructureConstants γ a) (h01 : a 0 0 * a 0 1 = (q : k)) :
    ∃ δa : ℕ → Fin 2 → k, (∀ i, δa 0 i = 0) ∧
      ∀ (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F),
        (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis
            ((algebraMap k (DualNumber k)).comp j₀) γ' →
        ¬ (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).HasStructureConstants γ'
            (fun m i => algebraMap k (DualNumber k) (a m i) + δa m i • DualNumber.eps) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and.solution
