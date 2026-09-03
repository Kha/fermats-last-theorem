import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
namespace P2MW.S_ModularCurve_JZero_finite_torsion_pow_of_cardinalityAJ

open AlgebraicCurve ModularCurve

def Pic0TorsionEquivSubtype (K F : Type*) [Field K] [Field F] [Algebra K F] (n : ℕ) :
    Pic0.torsion K F n ≃ {x : Pic0 K F // n • x = 0} :=
  Equiv.subtypeEquivRight (fun x => (Pic0.mem_torsion).trans (by rw [natCast_zsmul]))

theorem Pic0.natCard_torsion_eq_natCard_subtype (K F : Type*) [Field K] [Field F] [Algebra K F]
    (n : ℕ) : Nat.card (Pic0.torsion K F n) = Nat.card {x : Pic0 K F // n • x = 0} :=
  Nat.card_congr (Pic0TorsionEquivSubtype K F n)

theorem solution (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    (hK1 : CardinalityAJ p (JZero N) (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
    (k : ℕ) : Finite (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k)) := by
  apply Nat.finite_of_card_ne_zero
  rw [Pic0.natCard_torsion_eq_natCard_subtype]
  have h := hK1 k
  rw [h]
  exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
