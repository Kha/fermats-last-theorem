import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace K73GA

theorem isNilpotent_natCast_of_ringHom {p : ℕ} {B C : Type} [CommRing B] [CommRing C] (f : B →+* C)
    (hB : IsNilpotent (p : B)) : IsNilpotent (p : C) := by
  obtain ⟨n, hn⟩ := hB
  exact ⟨n, by rw [← map_natCast f, ← map_pow, hn, map_zero]⟩

end K73GA

theorem solution
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (g : B) :
    t.IsGradedS ι ψ (Rigidified.awayHom g) ∧ t.IsGradedSbar ι ψ (Rigidified.awayHom g) ∧
      Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom g) := by
  have hS : IsNilpotent (p : Rigidified.Baway g) :=
    K73GA.isNilpotent_natCast_of_ringHom (Rigidified.awayHom g) hB
  have hSbar : IsNilpotent (p : Rigidified.Baway g ⧸ pIdeal p (Rigidified.Baway g)) :=
    K73GA.isNilpotent_natCast_of_ringHom ((Ideal.Quotient.mk _).comp (Rigidified.awayHom g)) hB
  exact ⟨CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hS _,
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hSbar _,
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hSbar _⟩
