import Mathlib
import P2M.Util
namespace P2MW.S_Polynomial_abv_eval_le_gaussNorm

set_option autoImplicit false

open Polynomial

theorem solution {R : Type*} [CommRing R] (v : AbsoluteValue R ℝ)
    (hv : IsNonarchimedean v) {c : ℝ} (hc : 0 ≤ c) (p : R[X]) {z : R} (hz : v z ≤ c) :
    v (p.eval z) ≤ p.gaussNorm v c := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp [Subsingleton.elim p 0]
  rw [Polynomial.eval_eq_sum_range]
  obtain ⟨j, -, hj⟩ := IsNonarchimedean.finset_image_add_of_nonempty hv
    (fun i => p.coeff i * z ^ i) Finset.nonempty_range_add_one
  calc v (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * z ^ i)
      ≤ v (p.coeff j * z ^ j) := hj
    _ = v (p.coeff j) * v z ^ j := by rw [map_mul, map_pow]
    _ ≤ v (p.coeff j) * c ^ j := by gcongr
    _ ≤ p.gaussNorm v c := p.le_gaussNorm v hc j
