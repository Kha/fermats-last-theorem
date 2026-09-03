import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
namespace P2MW.S_LanglandsTunnell_CubicInduction_isCompact_localMaximalCompact3

set_option autoImplicit false

open IsDedekindDomain NumberField

open LanglandsTunnell.CubicInduction

noncomputable section

open Matrix

private theorem isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers ℚ)))

private def integralMatrices3 (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submonoid (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) where
  carrier := {a | ∀ i j, Valued.v (a i j) ≤ 1}
  one_mem' := by
    intro i j
    exact valued_one_entry_le3 (𝓞 ℚ) ℚ v i j
  mul_mem' := by
    intro a b ha hb i j
    exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => ha i l) (fun l => hb l j)

private theorem mem_integralMatrices3 (v : HeightOneSpectrum (𝓞 ℚ)) {a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} :
    a ∈ integralMatrices3 v ↔ ∀ i j, Valued.v (a i j) ≤ 1 :=
  Iff.rfl

private theorem isCompact_integralMatrices3 (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsCompact (integralMatrices3 v : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by
  have hpi : IsCompact (Set.pi Set.univ fun _ : Fin 3 =>
      Set.pi Set.univ fun _ : Fin 3 => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_adicCompletionIntegers v
  have hset : (integralMatrices3 v : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) =
      (Set.pi Set.univ fun _ : Fin 3 =>
        Set.pi Set.univ fun _ : Fin 3 => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) := by
    ext a
    rw [SetLike.mem_coe, mem_integralMatrices3]
    constructor
    · intro h i _ j _
      exact h i j
    · intro h i j
      exact h i (Set.mem_univ i) j (Set.mem_univ j)
  rw [hset]
  exact hpi

private theorem localMaximalCompact3_eq_units (v : HeightOneSpectrum (𝓞 ℚ)) :
    localMaximalCompact3 (𝓞 ℚ) ℚ v = (integralMatrices3 v).units := by
  ext k
  simp only [mem_localMaximalCompact3_iff, Submonoid.mem_units_iff, mem_integralMatrices3]

theorem solution (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsCompact ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  rw [localMaximalCompact3_eq_units]
  exact Submonoid.units_isCompact (isCompact_integralMatrices3 v)
