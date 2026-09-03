import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CritChartEndMatrix
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_CritChart_exists_basis_coe_eq_and_injective_endMatrix_of_forall_existsUnique_of_isCompl
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup open MvFormalGroup.CartierModule hiding eq_of_map_eq

theorem CerednikDrinfeld.FormalODModule.CritChart.exists_basis_coe_eq_and_injective_endMatrix_of_forall_existsUnique_of_isCompl
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [CharP B p] [IsDomain B]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B)
    (hLie : IsCompl (X.lieZero j) (X.lieOne j)) (i : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → MvFormalGroup.CartierModule p X.F)
    (he : ∀ r, e r ∈ CritChart.invariants X j i)
    (hrepr : ∀ m ∈ X.gradedPiece j i, ∃! w : ι → WittVector p B, m = ∑ r, w r • e r)
    (hfix : ∀ w : ι → WittVector p B,
      (∑ r, w r • e r) ∈ CritChart.invariants X j i ↔ ∀ r, WittVector.frobenius (w r) = w r) :
    ∃ β : Module.Basis ι ℤ_[p] (CritChart.invariantsSubmodule X j i),
      (∀ r, (β r : MvFormalGroup.CartierModule p X.F) = e r) ∧
      Function.Injective (CritChart.endMatrix X j i β) ∧
      Function.Injective (CritChart.endMatrixQ X j i β) ∧
      (∀ f, ∃ A : Matrix ι ι ℤ_[p], CritChart.endMatrixQ X j i β f = A.map ((↑) : ℤ_[p] → ℚ_[p])) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_CritChart_exists_basis_coe_eq_and_injective_endMatrix_of_forall_existsUnique_of_isCompl.solution
