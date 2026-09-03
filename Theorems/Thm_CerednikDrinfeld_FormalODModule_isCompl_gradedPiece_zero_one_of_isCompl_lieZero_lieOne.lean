import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [CharP B p]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B)
    (hLie : IsCompl (X.lieZero j) (X.lieOne j)) :
    IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1) ∧
    (∀ (n : ℕ) (g : MvFormalGroup.CartierModule p X.F),
        MvFormalGroup.CartierModule.verschiebung g ∈ X.gradedPiece j (n + 1) ↔
          g ∈ X.gradedPiece j n) ∧
    (∀ n, ∀ f ∈ X.gradedPiece j n,
        MvFormalGroup.CartierModule.frobenius f ∈ X.gradedPiece j (n + 1)) ∧
    (∀ n, ∀ f ∈ X.gradedPiece j n,
        MvFormalGroup.CartierModule.endAct X.varpiEnd f ∈ X.gradedPiece j (n + 1)) ∧
    (∀ (n : ℕ) (b : B), ∀ f ∈ X.gradedPiece j n,
        MvFormalGroup.CartierModule.homothety b f ∈ X.gradedPiece j n) ∧
    (∀ (n : ℕ) (a : CerednikDrinfeld.Zp2 p), ∀ f ∈ X.gradedPiece j n,
        MvFormalGroup.CartierModule.endAct (X.actEnd a) f ∈ X.gradedPiece j n) ∧
    (X.gradedPiece j 0).map MvFormalGroup.CartierModule.tangent = (X.lieZero j).toAddSubgroup ∧
    (X.gradedPiece j 1).map MvFormalGroup.CartierModule.tangent = (X.lieOne j).toAddSubgroup := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne.solution
