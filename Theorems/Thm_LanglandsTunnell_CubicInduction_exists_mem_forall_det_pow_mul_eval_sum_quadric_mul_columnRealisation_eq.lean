import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_mem_forall_det_pow_mul_eval_sum_quadric_mul_columnRealisation_eq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_mem_forall_det_pow_mul_eval_sum_quadric_mul_columnRealisation_eq
    (V : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (hsm : ∀ G ∈ V, WhittakerBlock.IsArchSmooth3 G)
    (hstab : ∀ G ∈ V, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ q : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ q k' = 1) →
      archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ V)
    (hflow : ∀ G ∈ V, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ V, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
        (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ) (j : Fin 3) (α : ℕ)
    (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ V)
    (hreal : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ α *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (p)) = G (WhittakerBlock.archRealLift3 o * k₁)) :
    (∀ a b : Fin 3, ∃ G' ∈ V, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ α *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          (∑ i : Fin 3, ∑ i' : Fin 3, MvPolynomial.X (i, a) * MvPolynomial.X (i', b) *
            MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (MvPolynomial.pderiv i (MvPolynomial.pderiv i' p))) =
      G' (WhittakerBlock.archRealLift3 o * k₁)) ∧
    (∀ a b : Fin 3, ∃ G' ∈ V, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ (α + 1) *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          (∑ i : Fin 3, ∑ i' : Fin 3, MvPolynomial.C (1 / 2 : ℂ) *
            (MvPolynomial.X (i, a) * MvPolynomial.X (i', b) + MvPolynomial.X (i, b) * MvPolynomial.X (i', a)) *
            MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (∑ c : Fin 3, ∑ d : Fin 3,
              MvPolynomial.C ((((i' : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
                (((d : ℕ) : ℂ) - ((i' : ℕ) : ℂ)) / 2) *
                (MvPolynomial.X c * MvPolynomial.pderiv d (MvPolynomial.pderiv i p)))) =
      G' (WhittakerBlock.archRealLift3 o * k₁)) ∧
    (∀ a b : Fin 3, ∃ G' ∈ V, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ α *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          (∑ i : Fin 3, ∑ i' : Fin 3, MvPolynomial.C (1 / 2 : ℂ) *
            (MvPolynomial.X (i, a) * MvPolynomial.X (i', b) + MvPolynomial.X (i, b) * MvPolynomial.X (i', a)) *
            MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (MvPolynomial.X i' * MvPolynomial.pderiv i p -
              MvPolynomial.C (1 / 3 : ℂ) * (∑ e : Fin 3, MvPolynomial.X e ^ 2) *
                MvPolynomial.pderiv i (MvPolynomial.pderiv i' p))) =
      G' (WhittakerBlock.archRealLift3 o * k₁)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_forall_det_pow_mul_eval_sum_quadric_mul_columnRealisation_eq.solution
