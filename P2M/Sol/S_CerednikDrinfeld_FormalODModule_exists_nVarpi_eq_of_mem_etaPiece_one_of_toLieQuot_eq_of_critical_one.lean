import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_one_of_toLieQuot_eq_of_critical_one

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (hEta1 : ∀ z : (X.toGradedCartierModuleData j hc).NMod, z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1 ↔
      ∃ m : MvFormalGroup.CartierModule p X.F, m ∈ X.gradedPiece j 1 ∧ MvFormalGroup.CartierModule.endAct X.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m ∧ z = (X.toGradedCartierModuleData j hc).nMk (m, 0))
    (hlift : ∀ m ∈ X.gradedPiece j 1, MvFormalGroup.CartierModule.endAct X.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m →
      (∃ m₀ ∈ X.gradedPiece j 0, ∃ g : MvFormalGroup.CartierModule p X.F, m = MvFormalGroup.CartierModule.endAct X.varpiEnd m₀ + MvFormalGroup.CartierModule.verschiebungInt g) →
        ∃ z₀ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0, (X.toGradedCartierModuleData j hc).lambda z₀ = m)
    (z : (X.toGradedCartierModuleData j hc).NMod) (hz : z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1)
    (htan : ∃ m₀ ∈ X.gradedPiece j 0, (X.toGradedCartierModuleData j hc).toLieQuot z = (X.toGradedCartierModuleData j hc).vRange.mkQ (MvFormalGroup.CartierModule.endAct X.varpiEnd m₀)) :
    ∃ z₀ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0, (X.toGradedCartierModuleData j hc).nVarpi z₀ = z := by
  classical
  have hDV : ∀ m : CartierModule p X.F, (X.toGradedCartierModuleData j hc).verschiebung m = verschiebungInt m := fun _ => rfl
  have hDPi : ∀ m : CartierModule p X.F, (X.toGradedCartierModuleData j hc).varpi m = endAct X.varpiEnd m := fun _ => rfl
  have hnv : ∀ m m' : CartierModule p X.F, (X.toGradedCartierModuleData j hc).nVarpi ((X.toGradedCartierModuleData j hc).nMk (m, m')) = (X.toGradedCartierModuleData j hc).nMk ((X.toGradedCartierModuleData j hc).varpi m, (X.toGradedCartierModuleData j hc).varpi m') :=
    fun _ _ => rfl
  obtain ⟨m, hm, hPV, rfl⟩ := (hEta1 z).1 hz
  obtain ⟨m₀, hm₀, htq⟩ := htan
  have hta : (X.toGradedCartierModuleData j hc).toLieQuot ((X.toGradedCartierModuleData j hc).nMk (m, 0)) = (X.toGradedCartierModuleData j hc).vRange.mkQ m := rfl
  rw [hta, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, (X.toGradedCartierModuleData j hc).mem_vRange_iff] at htq
  obtain ⟨g, hg⟩ := htq
  rw [← hDPi] at hg
  have hmeq : m = (X.toGradedCartierModuleData j hc).varpi m₀ + (X.toGradedCartierModuleData j hc).verschiebung g := (sub_eq_iff_eq_add'.1 hg.symm)
  obtain ⟨z₀, hz₀, hlam⟩ := hlift m hm hPV ⟨m₀, hm₀, g, hmeq⟩
  refine ⟨z₀, hz₀, ?_⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := (X.toGradedCartierModuleData j hc).nMk_surjective z₀
  rw [lambda_nMk] at hlam
  rw [hnv, ← hlam]
  have e : (((X.toGradedCartierModuleData j hc).varpi a, (X.toGradedCartierModuleData j hc).varpi b) : (X.toGradedCartierModuleData j hc).M × (X.toGradedCartierModuleData j hc).M) =
      ((X.toGradedCartierModuleData j hc).varpi a + (X.toGradedCartierModuleData j hc).verschiebung b, 0) - ((X.toGradedCartierModuleData j hc).verschiebung b, -(X.toGradedCartierModuleData j hc).varpi b) := by
    rw [Prod.mk_sub_mk, add_sub_cancel_right, zero_sub, neg_neg]
  rw [e, map_sub, nMk_verschiebung_neg_varpi, sub_zero]
