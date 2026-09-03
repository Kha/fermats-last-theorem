import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import P2M.Util
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt

set_option autoImplicit false

open IsDedekindDomain NumberField

open LanglandsTunnell.CubicInduction in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (hd : ¬ (Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1))) :
    ∃ (k₁ k₂ : ℕ) (c : ℤ), Valued.v (d 0) = WithZero.exp (-((k₁ : ℤ) + c)) ∧
      Valued.v (d 1) = WithZero.exp (-((k₂ : ℤ) + c)) ∧ Valued.v (d 2) = WithZero.exp (-c) := by
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero t
  rw [ht, Matrix.det_diagonal] at hdet
  have hne : ∀ i, Valued.v (d i) ≠ 0 := fun i =>
    (Valuation.ne_zero_iff _).mpr (Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i))
  obtain ⟨a, ha⟩ : ∃ a : Fin 3 → ℤ, ∀ i, WithZero.exp (a i) = Valued.v (d i) :=
    ⟨fun i => WithZero.log (Valued.v (d i)), fun i => WithZero.exp_log (hne i)⟩
  obtain ⟨h10, h21⟩ := not_or.mp hd
  have h01 : a 0 ≤ a 1 := by
    have h := not_lt.mp h10
    rw [← ha 0, ← ha 1] at h
    exact WithZero.exp_le_exp.mp h
  have h12 : a 1 ≤ a 2 := by
    have h := not_lt.mp h21
    rw [← ha 1, ← ha 2] at h
    exact WithZero.exp_le_exp.mp h
  refine ⟨(a 2 - a 0).toNat, (a 2 - a 1).toNat, -a 2, ?_, ?_, ?_⟩
  · rw [← ha 0, WithZero.exp_inj, Int.toNat_of_nonneg (by omega)]
    omega
  · rw [← ha 1, WithZero.exp_inj, Int.toNat_of_nonneg (by omega)]
    omega
  · rw [← ha 2, WithZero.exp_inj]
    omega
