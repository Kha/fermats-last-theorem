import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_eq_of_pow_of_pow

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] [Nontrivial B] {φ : Series B} {h h' : ℕ}
    (hh : FormalODModule.HasKernelOfDegree φ (p ^ h)) (hh' : FormalODModule.HasKernelOfDegree φ (p ^ h')) :
    h = h' := by
  classical
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal B
  letI : Field (B ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have e1 := hh.2.2 (B ⧸ 𝔪) (Ideal.Quotient.mk 𝔪)
  have e2 := hh'.2.2 (B ⧸ 𝔪) (Ideal.Quotient.mk 𝔪)
  have hp : p ^ h = p ^ h' := e1.symm.trans e2
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hp
