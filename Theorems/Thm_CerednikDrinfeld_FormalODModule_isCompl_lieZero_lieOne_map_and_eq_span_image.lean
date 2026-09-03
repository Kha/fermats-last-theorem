import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_isCompl_lieZero_lieOne_map_and_eq_span_image

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.isCompl_lieZero_lieOne_map_and_eq_span_image
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B)
    (hLie : IsCompl (X.lieZero j) (X.lieOne j))
    {B' : Type u} [CommRing B'] (f : B →+* B') :
    IsCompl ((X.map f).lieZero (f.comp j)) ((X.map f).lieOne (f.comp j)) ∧
    (X.map f).lieZero (f.comp j) =
      Submodule.span B' ((fun v : Fin 2 → B => ⇑f ∘ v) '' (X.lieZero j : Set (Fin 2 → B))) ∧
    (X.map f).lieOne (f.comp j) =
      Submodule.span B' ((fun v : Fin 2 → B => ⇑f ∘ v) '' (X.lieOne j : Set (Fin 2 → B))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_isCompl_lieZero_lieOne_map_and_eq_span_image.solution
