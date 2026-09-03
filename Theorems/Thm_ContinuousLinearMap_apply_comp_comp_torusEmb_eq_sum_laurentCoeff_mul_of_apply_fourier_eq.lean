import Mathlib
import P2M.Util
import P2M.Sol.S_ContinuousLinearMap_apply_comp_comp_torusEmb_eq_sum_laurentCoeff_mul_of_apply_fourier_eq

set_option autoImplicit false

open MeasureTheory

theorem ContinuousLinearMap.apply_comp_comp_torusEmb_eq_sum_laurentCoeff_mul_of_apply_fourier_eq
    {ιL : Type} (d : ℕ) (XK : Set (Fin d → ℂ × ℂ)) (X : Set (ιL → ℂ × ℂ))
    (emb : C((Fin d → AddCircle (1 : ℝ)), XK))
    (hemb : ∀ (θ : Fin d → AddCircle (1 : ℝ)) (i : Fin d),
      ((emb θ : XK) : Fin d → ℂ × ℂ) i = ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))
    (w' : Fin d → ιL) (ρ s ζ N : Fin d → ℂ) (hN : ∀ i : Fin d, N i ≠ 0)
    (bc : C(XK, X))
    (hbc1 : ∀ (x : XK) (i : Fin d), (((bc x : X) : ιL → ℂ × ℂ) (w' i)).1 =
      ρ i * s i * ((((x : XK) : Fin d → ℂ × ℂ) i).1 + (((x : XK) : Fin d → ℂ × ℂ) i).2))
    (hbc2 : ∀ (x : XK) (i : Fin d), (((bc x : X) : ιL → ℂ × ℂ) (w' i)).2 =
      N i * ζ i + ((((x : XK) : Fin d → ℂ × ℂ) i).1 * (((x : XK) : Fin d → ℂ × ℂ) i).2 - 1))
    (μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ) (c : (Fin d → ℤ) → ℂ)
    (hc : ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) → μ e = c n)
    (ks js : Fin d → ℕ) (g : C(X, ℂ))
    (hg : ∀ x : X, g x = ∏ i : Fin d,
      (((x : X) : ιL → ℂ × ℂ) (w' i)).1 ^ ks i * ((N i)⁻¹ * (((x : X) : ιL → ℂ × ℂ) (w' i)).2) ^ js i) :
    μ ((g.comp bc).comp emb) =
      ∑ n ∈ Fintype.piFinset (fun i : Fin d => Finset.Icc (-(ks i : ℤ)) (ks i)),
        (∏ i : Fin d, (ρ i * s i) ^ ks i * ζ i ^ js i *
          ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks i : LaurentPolynomial ℂ).coeff (n i)) * c n := by p2m_exact_reverting @_root_.P2MW.S_ContinuousLinearMap_apply_comp_comp_torusEmb_eq_sum_laurentCoeff_mul_of_apply_fourier_eq.solution
