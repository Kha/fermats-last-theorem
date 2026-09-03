import Definitions.Def_ExtEndgame_ProductionDatum
import Theorems.Thm_groupCohomology_natCard_continuousClasses_ofChar_cycloChar_eq_natCard_units_quot_of_primeLocal
import Theorems.Thm_Padic_natCard_units_quot_range_powMonoidHom_of_ne_two
import P2M.Util
namespace P2MW.S_groupCohomology_finrank_continuousClasses_ofChar_cycloChar_eq_two_of_primeLocal
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
open scoped IntermediateField Pointwise

theorem solution
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (q : Nat.Primes) (hq : (q : ℕ) = p)
    (adm₁ : Submodule (ZMod p) (H1 (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))
    (hadm₁ : ∀ x, x ∈ adm₁ ↔
      ∃ c : cocycles₁ (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ (g s : primeLocalGaloisGroup q),
            primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
        ∧ (H1π _).hom c = x) :
    Module.Finite (ZMod p) adm₁ ∧ finrank (ZMod p) adm₁ = 2 := by
  have hcard : Nat.card adm₁ = p ^ 2 := by
    rw [natCard_continuousClasses_ofChar_cycloChar_eq_natCard_units_quot_of_primeLocal q hq adm₁ hadm₁,
      Padic.natCard_units_quot_range_powMonoidHom_of_ne_two hp2]
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : Finite adm₁ := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp0)
  haveI : Module.Finite (ZMod p) adm₁ := Module.Finite.of_finite
  refine ⟨inferInstance, ?_⟩
  have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := adm₁)
  rw [hcard, Nat.card_zmod] at h
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
