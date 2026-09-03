import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import P2M.Util
namespace P2MW.S_LanglandsTunnell_CubicInduction_mul_mem_congruenceK1

set_option autoImplicit false

open Matrix IsDedekindDomain
open LanglandsTunnell.CubicInduction

namespace CongruenceBottomEntries

private theorem mem_congruenceK1_iff_bottom_sub_one (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (c : ℕ) (k : GL (Fin 3) (v.adicCompletion K)) :
    k ∈ congruenceK1 R K v c ↔
      k ∈ localMaximalCompact3 R K v ∧
        ∀ l : Fin 3,
          Valued.v (((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) - 1) 2 l) ≤ WithZero.exp (-(c : ℤ)) := by
  rw [mem_congruenceK1_iff]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨h0, ?_⟩
    intro l
    fin_cases l
    · simpa [Matrix.sub_apply, Matrix.one_apply] using h1
    · simpa [Matrix.sub_apply, Matrix.one_apply] using h2
    · simpa [Matrix.sub_apply, Matrix.one_apply] using h3
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_, ?_, ?_⟩
    · simpa [Matrix.sub_apply, Matrix.one_apply] using h 0
    · simpa [Matrix.sub_apply, Matrix.one_apply] using h 1
    · simpa [Matrix.sub_apply, Matrix.one_apply] using h 2

end CongruenceBottomEntries

open CongruenceBottomEntries

theorem solution
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) {c : ℕ}
    {k k' : GL (Fin 3) (v.adicCompletion K)} (hk : k ∈ congruenceK1 R K v c) (hk' : k' ∈ congruenceK1 R K v c) :
    k * k' ∈ congruenceK1 R K v c := by
  obtain ⟨hk0, hk1⟩ := (mem_congruenceK1_iff_bottom_sub_one R K v c k).1 hk
  obtain ⟨hk0', hk1'⟩ := (mem_congruenceK1_iff_bottom_sub_one R K v c k').1 hk'
  refine (mem_congruenceK1_iff_bottom_sub_one R K v c (k * k')).2 ⟨mul_mem hk0 hk0', fun l => ?_⟩
  have hsplit : ((k * k' : GL (Fin 3) (v.adicCompletion K)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) - 1 =
      ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) - 1) * (k' : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) +
        ((k' : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) - 1) := by
    rw [Units.val_mul, sub_mul, one_mul]
    abel
  rw [hsplit, Matrix.add_apply]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hk1' l))
  exact valued_mul_apply_le3 R K v hk1 (fun m => hk0'.1 m l)
