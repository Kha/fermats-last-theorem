import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_eq_of_span_eq_top

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_forall_map_eq_of_span_eq_top
    (𝒪 : Type) [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)
    (B : Type) [CommRing B] [Algebra 𝒪 B]
    (n : ℕ) (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)] [∀ i, Algebra 𝒪 (L i)]
    [∀ i, IsScalarTower 𝒪 B (L i)] [∀ i, IsLocalization.Away (f i) (L i)]
    (d d' : OmegaObj (K := K) π B)
    (h : ∀ i, DeligneDatum.map π (IsScalarTower.toAlgHom 𝒪 B (L i)) d =
      DeligneDatum.map π (IsScalarTower.toAlgHom 𝒪 B (L i)) d') : d = d' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_eq_of_span_eq_top.solution
