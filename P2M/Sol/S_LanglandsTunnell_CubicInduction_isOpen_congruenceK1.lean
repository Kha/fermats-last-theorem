import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3
import P2M.Util
namespace P2MW.S_LanglandsTunnell_CubicInduction_isOpen_congruenceK1

set_option autoImplicit false

open Matrix IsDedekindDomain

open LanglandsTunnell.CubicInduction

namespace CongruenceBottomRow

open Matrix IsDedekindDomain NumberField

section BottomRow

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

private def bottomRowConditions (c : ℕ) : Set (GL (Fin 3) (v.adicCompletion K)) :=
  {k | Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 0) ≤ WithZero.exp (-(c : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 1) ≤ WithZero.exp (-(c : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 2 - 1) ≤ WithZero.exp (-(c : ℤ))}

private theorem congruenceK1_eq_inter (c : ℕ) :
    LanglandsTunnell.CubicInduction.congruenceK1 R K v c =
      ((LanglandsTunnell.CubicInduction.localMaximalCompact3 R K v :
          Subgroup (GL (Fin 3) (v.adicCompletion K))) : Set (GL (Fin 3) (v.adicCompletion K))) ∩
        bottomRowConditions R K v c :=
  Set.ext fun _ => Iff.rfl

private theorem continuous_entry (i j : Fin 3) :
    Continuous fun k : GL (Fin 3) (v.adicCompletion K) => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j :=
  Units.continuous_val.matrix_elem i j

private theorem bottomRowConditions_eq (c : ℕ) :
    bottomRowConditions R K v c =
      (fun k : GL (Fin 3) (v.adicCompletion K) => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 0) ⁻¹'
          {y | Valued.v y ≤ WithZero.exp (-(c : ℤ))} ∩
        ((fun k : GL (Fin 3) (v.adicCompletion K) => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 1) ⁻¹'
            {y | Valued.v y ≤ WithZero.exp (-(c : ℤ))} ∩
          (fun k : GL (Fin 3) (v.adicCompletion K) =>
              (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 2 - 1) ⁻¹'
            {y | Valued.v y ≤ WithZero.exp (-(c : ℤ))}) :=
  Set.ext fun _ => Iff.rfl

private theorem isOpen_bottomRowConditions (c : ℕ) : IsOpen (bottomRowConditions R K v c) := by
  obtain ⟨t, ht0, ht⟩ := AdelicLevel.exists_valued_eq_exp_neg (K := K) v c
  have hB : IsOpen {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(c : ℤ))} := by
    rw [← ht]
    exact AdelicLevel.isOpen_setOf_valued_le (K := K) v t ht0
  rw [bottomRowConditions_eq R K v c]
  exact (hB.preimage (continuous_entry R K v 2 0)).inter
    ((hB.preimage (continuous_entry R K v 2 1)).inter
      (hB.preimage ((continuous_entry R K v 2 2).sub continuous_const)))

end BottomRow

end CongruenceBottomRow

open CongruenceBottomRow

theorem solution
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (c : ℕ) :
    IsOpen (congruenceK1 R K v c) := by
  rw [congruenceK1_eq_inter R K v c]
  exact (isOpen_localMaximalCompact3 R K v).inter (isOpen_bottomRowConditions R K v c)
