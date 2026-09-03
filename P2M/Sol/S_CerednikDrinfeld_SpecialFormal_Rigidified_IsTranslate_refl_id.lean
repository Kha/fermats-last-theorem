import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsTranslate_refl_id

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem frobSeries_zero {p : ℕ} [Fact p.Prime] (B : Type) [CommRing B] : Rigidified.frobSeries (p := p) B 0 = Series.id B := by
  funext i
  simp [Rigidified.frobSeries, Series.id]

theorem solution
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B) :
    Rigidified.IsTranslate (Series.id (O ⧸ pIdeal p O)) 0 0 ψ t t := by
  refine ⟨rfl, 0, ?_⟩
  rw [mul_zero, frobSeries_zero]
  rw [Series.map_id, Series.comp_id, Series.comp_id, Series.comp_id, add_zero]
