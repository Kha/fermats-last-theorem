module

public import Definitions.Def_ModularCurve_ArithmeticGalois
public import Definitions.Def_ModularCurve_JqCoeff
public import Definitions.Def_ModularCurve_PhiGen
public import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental
public import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily
public import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull
public import Theorems.Thm_ModularCurve_transcendental_jqModC
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull

noncomputable section
open IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldFull laurentBaseChange jqModC jqNModC jqNModC_one ModularPolynomialFamily isIntegral_jqNModC_all_of_modularPolynomialFamily laurentBaseChange_modularFunctionFieldFull transcendental_jqModC"
p2m_open "ModularCurve"
namespace R8

def gens (L : Type*) [Field L] (N : ℕ) : Finset (LaurentSeries L) := by
  classical
  exact Finset.univ.image fun d : {d // d ∈ N.divisors} =>
    @jqNModC L _ d.1 ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors d.2)⟩

theorem mem_gens_iff (L : Type*) [Field L] (N : ℕ) [NeZero N] (x : LaurentSeries L) :
    x ∈ gens L N ↔ ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = jqNModC L d := by
  classical
  unfold gens
  constructor
  · intro hx
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨d.1, ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors d.2)⟩, Nat.dvd_of_mem_divisors d.2, rfl⟩
  · rintro ⟨d, hd, hdN, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨d, Nat.mem_divisors.mpr ⟨hdN, NeZero.ne N⟩⟩, Finset.mem_univ _, rfl⟩

theorem insert_gens (L : Type*) [Field L] (N : ℕ) [NeZero N] :
    insert (jqModC L) (gens L N : Set (LaurentSeries L)) = {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = jqNModC L d} := by
  ext x
  simp only [Set.mem_insert_iff, Finset.mem_coe, mem_gens_iff, Set.mem_setOf_eq]
  constructor
  · rintro (rfl | h)
    · exact ⟨1, inferInstance, one_dvd N, (jqNModC_one L).symm⟩
    · exact h
  · exact Or.inr

end R8
end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull.ModularCurve AlgebraicCurve"

theorem solution (L : Type*) [Field L] [Algebra ℚ L]
    (hΦ : ModularPolynomialFamily) (N : ℕ) [NeZero N] :
    HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull N)) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  -- The goal carries the shortcut instance `instAlgebraLaurentBaseChange L (modularFunctionFieldFull N)`,
  -- which does not abstract over the rewritten field, so rewriting the goal fails with an ill-typed
  -- motive; rewrite the hypothesis (generic instance) instead and convert.
  have h := AlgebraicCurve.hasPrincipalDivisors_adjoin_of_transcendental L (jqModC L) (transcendental_jqModC L)
    (ModularCurve.R8.gens L N) (fun t ht => by
      obtain ⟨d, hd, -, rfl⟩ := (ModularCurve.R8.mem_gens_iff L N t).mp ht
      exact isIntegral_jqNModC_all_of_modularPolynomialFamily L hΦ d)
  rw [ModularCurve.R8.insert_gens, ← laurentBaseChange_modularFunctionFieldFull] at h
  exact h

end
