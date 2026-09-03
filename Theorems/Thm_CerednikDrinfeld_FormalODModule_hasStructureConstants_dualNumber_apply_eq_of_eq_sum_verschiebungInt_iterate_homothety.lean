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
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule in

theorem CerednikDrinfeld.FormalODModule.hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    (j₀ : Zp2 q →+* k) (X₀ : FormalODModule q k)
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.IsHomogeneousVBasis j₀ γ)
    (a : ℕ → Fin 2 → k) (ha : X₀.HasStructureConstants γ a)
    (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hγ' : (X₀.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀) γ')
    (s v w : Fin 2 → k) (g : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hshape : ∀ i, γ' i =
      MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (1 + s i • DualNumber.eps)
          (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (v i • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ (FormalODModule.piIndex 0 i)) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[2]
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (w i • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[3] (g i))
    (a' : ℕ → Fin 2 → DualNumber k) (ha' : (X₀.map (algebraMap k (DualNumber k))).HasStructureConstants γ' a') :
    (∀ i, a' 0 i = algebraMap k (DualNumber k) (a 0 i) +
        ((s i - s (FormalODModule.piIndex 0 i)) * a 0 i) • DualNumber.eps) ∧
    (∀ i, a' 1 i = algebraMap k (DualNumber k) (a 1 i) +
        (v i * a 0 (FormalODModule.piIndex 0 i) - a 0 i ^ q * v (FormalODModule.piIndex 0 i) - a 1 i * s i) •
          DualNumber.eps) ∧
    (∀ i₀, a 0 i₀ = 0 →
      (∃ y : MvFormalGroup.CartierModule q X₀.F,
        MvFormalGroup.CartierModule.frobenius (γ i₀) = MvFormalGroup.CartierModule.verschiebungInt y) →
      a' 2 i₀ = algebraMap k (DualNumber k) (a 2 i₀) -
        (a 1 i₀ ^ q * v i₀ + a 2 i₀ * s (FormalODModule.piIndex 0 i₀)) • DualNumber.eps) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.solution
