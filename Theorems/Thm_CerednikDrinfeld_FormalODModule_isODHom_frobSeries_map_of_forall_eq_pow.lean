import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_isODHom_frobSeries_map_of_forall_eq_pow

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.isODHom_frobSeries_map_of_forall_eq_pow
    {p : ℕ} [Fact p.Prime] {C : Type} [CommRing C] {D : Type} [CommRing D]
    (f g : C →+* D) (j : ℕ) (hp : (p : D) = 0) (hg : ∀ x : C, g x = (f x) ^ (p ^ j))
    (G : FormalODModule p C) :
    FormalODModule.IsODHom (G.map f) (G.map g) (Rigidified.frobSeries (p := p) D j) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_isODHom_frobSeries_map_of_forall_eq_pow.solution
