import Mathlib
import P2M.Util
namespace P2MW.S_ValuationSubring_mem_nonunits_iff_map_mem_nonunits_of_forall_mem_iff

namespace G4GaussS

lemma mem_nonunits_iff_mem_and {K : Type} [Field K] (W : ValuationSubring K) (f : K) :
    f ∈ W.nonunits ↔ f ∈ W ∧ (f = 0 ∨ f⁻¹ ∉ W) := by
  rw [ValuationSubring.mem_nonunits_iff]
  constructor
  · intro hlt
    have hf : f ∈ W := (ValuationSubring.valuation_le_one_iff _ _).mp hlt.le
    refine ⟨hf, ?_⟩
    by_cases hf0 : f = 0
    · exact Or.inl hf0
    · right
      intro hinv
      have hunit : IsUnit (⟨f, hf⟩ : ↥W) :=
        isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0)⟩
      have h1 := (ValuationSubring.valuation_eq_one_iff _ _).mp hunit
      have h1' : W.valuation f = 1 := h1
      rw [h1'] at hlt
      exact lt_irrefl _ hlt
  · rintro ⟨hf, h⟩
    rcases h with hf0 | hinv
    · rw [hf0, map_zero]
      exact zero_lt_one
    · rcases ValuationSubring.valuation_lt_one_or_eq_one W ⟨f, hf⟩ with hlt | h1
      · exact hlt
      · exfalso
        have hunit : IsUnit (⟨f, hf⟩ : ↥W) := (ValuationSubring.valuation_eq_one_iff _ _).mpr h1
        obtain ⟨g, hg⟩ := hunit.exists_right_inv
        have hg1 : f * (g : K) = 1 := congrArg Subtype.val hg
        have hf0 : f ≠ 0 := left_ne_zero_of_mul (by rw [hg1]; exact one_ne_zero)
        have hg2 : (g : K) = f⁻¹ := by
          rw [← mul_one f⁻¹, ← hg1, inv_mul_cancel_left₀ hf0]
        exact hinv (hg2 ▸ g.2)

end G4GaussS

open G4GaussS in
theorem solution
    (K K' : Type) [Field K] [Field K'] (ι : K →+* K')
    (W : ValuationSubring K) (W' : ValuationSubring K')
    (h : ∀ f : K, f ∈ W ↔ ι f ∈ W') (f : K) :
    f ∈ W.nonunits ↔ ι f ∈ W'.nonunits := by
  rw [mem_nonunits_iff_mem_and W f, mem_nonunits_iff_mem_and W' (ι f), h f, h f⁻¹, map_inv₀,
    map_eq_zero_iff ι ι.injective]

#print axioms solution
