import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul

set_option autoImplicit false

open scoped TensorProduct
theorem LanglandsTunnell.CubicInduction.exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))
    (hanti : ∀ (i j : Fin 3) (x : W), ρ j i x = -ρ i j x)
    (hcas : ∀ x : W, ρ 0 1 (ρ 0 1 x) + ρ 0 2 (ρ 0 2 x) + ρ 1 2 (ρ 1 2 x) = -((2 : ℂ) • x))
    (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w : W, w ≠ 0 → 0 < (B w w).re)
    (hskew : ∀ (i j : Fin 3) (x y : W), B (ρ i j x) y = -B x (ρ i j y))
    (N : ℕ) :
    let Y : Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      Matrix.of fun a b => if h : a ≤ b then MvPolynomial.X ⟨(a, b), h⟩ else MvPolynomial.X ⟨(b, a), le_of_not_ge h⟩
    let K : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => Matrix.single i j 1 - Matrix.single j i 1
    let D : Fin 3 → Fin 3 →
        Derivation ℂ (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ)
          (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => MvPolynomial.mkDerivation ℂ fun v => (K i j * Y - Y * K i j) v.1.1 v.1.2
    let θ : Fin 3 → Fin 3 → (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W →ₗ[ℂ] MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W) :=
      fun i j => TensorProduct.map LinearMap.id (ρ i j) - TensorProduct.map (D i j).toLinearMap LinearMap.id
    let S : Submodule ℂ (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W) :=
      Submodule.span ℂ {x : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W | ∃ (q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W), q.IsHomogeneous N ∧ x = q ⊗ₜ[ℂ] w}
    Module.Finite ℂ S ∧
    (∀ i j : Fin 3, ∀ x ∈ S, θ i j x ∈ S) ∧
    (∃ B' : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W → MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W → ℂ,
      (∀ (z : ℂ), ∀ w₁ ∈ S, ∀ w₂ ∈ S, ∀ w' ∈ S, B' (z • w₁ + w₂) w' = z * B' w₁ w' + B' w₂ w') ∧
      (∀ w ∈ S, ∀ w' ∈ S, B' w' w = (starRingEnd ℂ) (B' w w')) ∧
      (∀ w ∈ S, w ≠ 0 → 0 < (B' w w).re) ∧
      (∀ i j : Fin 3, ∀ w ∈ S, ∀ w' ∈ S, B' (θ i j w) w' = -B' w (θ i j w'))) ∧
    (∀ (q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W),
      (θ 0 1 ∘ₗ θ 0 1 + θ 0 2 ∘ₗ θ 0 2 + θ 1 2 ∘ₗ θ 1 2) (q ⊗ₜ[ℂ] w) + (2 : ℂ) • (q ⊗ₜ[ℂ] w) =
        ((D 0 1 (D 0 1 q)) ⊗ₜ[ℂ] w - ((D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w) + (D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w))) +
        ((D 0 2 (D 0 2 q)) ⊗ₜ[ℂ] w - ((D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w) + (D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w))) +
        ((D 1 2 (D 1 2 q)) ⊗ₜ[ℂ] w - ((D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w) + (D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w)))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.solution
