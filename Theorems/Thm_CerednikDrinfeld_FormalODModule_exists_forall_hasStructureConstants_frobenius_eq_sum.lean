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
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_forall_hasStructureConstants_frobenius_eq_sum

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.exists_forall_hasStructureConstants_frobenius_eq_sum
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [Algebra (PadicInt p) B]
    (j : CerednikDrinfeld.Zp2 p →+* B) (a : ℕ → Fin 2 → B) :
    ∃ c : ℕ → Fin 2 → Fin 2 → B,
      ∀ (X : CerednikDrinfeld.FormalODModule p B) (γ : Fin 2 → MvFormalGroup.CartierModule p X.F),
        X.IsHomogeneousVBasis j γ → X.HasStructureConstants γ a →
        ∀ (i : Fin 2) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p X.F,
          MvFormalGroup.CartierModule.frobenius (γ i) =
            (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))^[(m : ℕ)]
              (∑ k : Fin 2, MvFormalGroup.CartierModule.homothety (c m i k) (γ k))) +
            (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))^[N] h := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_forall_hasStructureConstants_frobenius_eq_sum.solution
