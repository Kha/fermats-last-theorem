import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
namespace P2MW.S_ModularCurve_genusFormula_nine

set_option autoImplicit false

namespace Ws23
namespace GenusNumerics9
open ModularCurve

theorem divisors_eq : Nat.divisors 9 = {1, 3, 9} := by decide

theorem dedekindPsi_eq : dedekindPsi 9 = 12 := by
  rw [dedekindPsi, divisors_eq]
  have h1 : Squarefree (1 : ℕ) := squarefree_one
  have h3 : Squarefree (3 : ℕ) := Nat.prime_three.prime.squarefree
  have h9 : ¬ Squarefree (9 : ℕ) := fun h => by
    have := h 3 ⟨1, by norm_num⟩
    rw [Nat.isUnit_iff] at this; omega
  rw [Finset.filter_insert, if_pos h1, Finset.filter_insert, if_pos h3, Finset.filter_singleton, if_neg h9]
  decide

theorem cuspCount_eq : cuspCount 9 = 4 := by decide

theorem nuTwo_eq : nuTwo 9 = 0 := by
  rw [nuTwo, Nat.card_eq_fintype_card]; decide

theorem nuThree_eq : nuThree 9 = 0 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide

theorem main : genusFormula 9 = 0 := by
  rw [genusFormula, dedekindPsi_eq, cuspCount_eq, nuTwo_eq, nuThree_eq]
  norm_num

end Ws23.GenusNumerics9

theorem solution : ModularCurve.genusFormula 9 = 0 :=
  Ws23.GenusNumerics9.main
