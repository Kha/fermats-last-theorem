import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
namespace P2MW.S_MvFormalGroup_nilEval_X_of_mem

set_option autoImplicit false

open MvPowerSeries

theorem solution
    {σ : Type} [Fintype σ] [DecidableEq σ] {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    (J : Ideal B') (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (s : σ → B') (hs : ∀ i, s i ∈ J) (i : σ) :
    MvFormalGroup.nilEval n (MvPowerSeries.X i : MvPowerSeries σ B) s = s i := by
  classical
  unfold MvFormalGroup.nilEval
  by_cases hn : n = 0
  ·
    subst hn
    have hJ0 : J = ⊥ := by simpa using hJ
    have hs0 : s i = 0 := by simpa [hJ0] using hs i
    have ht : MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ : σ => (0 : ℕ)) (MvPowerSeries.X i : MvPowerSeries σ B) = 0 := by
      apply MvPolynomial.ext
      intro m
      rw [MvPowerSeries.coeff_trunc', MvPolynomial.coeff_zero, MvPowerSeries.coeff_X]
      split_ifs with h1 h2
      ·
        exfalso
        have : m i ≤ 0 := by
          have := h1 i
          simpa using this
        rw [h2] at this
        simp at this
      · rfl
      · rfl
    rw [ht, map_zero, hs0]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have ht : MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ : σ => n) (MvPowerSeries.X i : MvPowerSeries σ B) =
        MvPolynomial.X i := by
      apply MvPolynomial.ext
      intro m
      rw [MvPowerSeries.coeff_trunc', MvPowerSeries.coeff_X, MvPolynomial.coeff_X']
      by_cases hm : m = Finsupp.single i 1
      · subst hm
        have hle : Finsupp.single i 1 ≤ Finsupp.equivFunOnFinite.symm (fun _ : σ => n) := by
          rw [Finsupp.single_le_iff]
          simpa using hn1
        simp [hle]
      · simp [hm, Ne.symm hm]
    rw [ht, MvPolynomial.aeval_X]
