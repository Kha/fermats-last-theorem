import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsTranslate_refl_id

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsTranslate.refl_id
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B) :
    Rigidified.IsTranslate (Series.id (O ⧸ pIdeal p O)) 0 0 ψ t t := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsTranslate_refl_id.solution
