import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_WittVector_ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent

set_option autoImplicit false

universe u v

open CerednikDrinfeld

theorem WittVector.ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] (hp : IsNilpotent (p : R))
    {A : Type v} [Ring A] [Algebra R A]
    (ρ : Zp2 p →+* A) (j : Zp2 p →+* R) (a : Zp2 p) (ha : WittVector.frobenius a = a) :
    ρ a = algebraMap R A (j a) := by p2m_exact_reverting @_root_.P2MW.S_WittVector_ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent.solution
