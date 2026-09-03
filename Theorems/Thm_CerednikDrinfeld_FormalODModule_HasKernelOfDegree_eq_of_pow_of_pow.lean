import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_eq_of_pow_of_pow

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.HasKernelOfDegree.eq_of_pow_of_pow
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] [Nontrivial B] {φ : Series B} {h h' : ℕ}
    (hh : FormalODModule.HasKernelOfDegree φ (p ^ h)) (hh' : FormalODModule.HasKernelOfDegree φ (p ^ h')) :
    h = h' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_eq_of_pow_of_pow.solution
