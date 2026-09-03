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
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule in

theorem CerednikDrinfeld.FormalODModule.exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    (j₀ : Zp2 q →+* k) (X₀ : FormalODModule q k)
    (hLie : IsCompl (X₀.lieZero j₀) (X₀.lieOne j₀))
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.IsHomogeneousVBasis j₀ γ)
    (hF : (X₀.map (algebraMap k (DualNumber k))).F.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.F)
    (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hγ' : (X₀.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀) γ')
    (hred : ∀ i, MvFormalGroup.CartierModule.baseChangeEq (TrivSqZeroExt.fstHom k k k).toRingHom hF (γ' i) = γ i)
    (i : Fin 2) (N : ℕ) :
    ∃ (c : Fin N → DualNumber k) (g : MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F),
      g ∈ (X₀.map (algebraMap k (DualNumber k))).gradedPiece ((algebraMap k (DualNumber k)).comp j₀) (i + N) ∧
      γ' i =
        (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[(m : ℕ)]
          (MvFormalGroup.CartierModule.homothety (c m)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k))
              (γ (FormalODModule.piIndex ((m : ℕ) + 1) i))))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[N] g ∧
      (∀ m : Fin N, (m : ℕ) = 0 → TrivSqZeroExt.fst (c m) = 1) ∧
      (∀ m : Fin N, 1 ≤ (m : ℕ) → TrivSqZeroExt.fst (c m) = 0) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_eq_sum_verschiebungInt_iterate_homothety_baseChange_of_baseChangeEq_eq.solution
