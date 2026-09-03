import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Exponential
import P2M.Util
import P2M.Sol.S_RegularSingular_exists_transferMatrix_expLogExpansion_rescale_expTwist

set_option autoImplicit false

theorem RegularSingular.exists_transferMatrix_expLogExpansion_rescale_expTwist
    {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    (lam₀ : ℝ) (hlam₀ : 0 < lam₀) (hlam₀1 : lam₀ ≤ 1)
    (aB : ℝ) (Kd : ℕ) (hKd1 : aB / (Kd + 1) ≤ 1 / 2) (hKd2 : ∀ i, ρ + δ + 1 ≤ (e i).re + Kd)
    (Ω' : ℝ) (hΩ' : 0 ≤ Ω')
    (κ₀ a' : ℂ) (hκ₀ : ‖κ₀‖ ≤ Ω') (ha' : ‖a'‖ ≤ aB) (ha're : a'.re = 0)
    (lam : ℝ) (hlam : 0 < lam) (hlam_ge : lam₀ ≤ lam) (hlam_le : lam ≤ lam₀⁻¹) :
    ∃ L : Fin n → Fin J → Fin n → Fin J → ℂ,
      (∀ i k i₀ m, ‖L i k i₀ m‖ ≤ Ω' * (Real.exp aB *
        (∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re))) * ((1 + |Real.log lam₀|) ^ J * 2 ^ J))) ∧
      ∀ (Bc' C₁' W₀ : ℝ), 0 ≤ Bc' → 0 ≤ C₁' → 0 ≤ W₀ →
      ∀ (G F : ℝ → ℂ) (c : Fin n → Fin J → ℂ), (∀ i j, ‖c i j‖ ≤ Bc') →
      (∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖G y - ∑ i : Fin n, ∑ j : Fin J, c i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
          C₁' * y ^ (ρ + δ)) →
      (∀ s : ℝ, lam₀ ≤ s → s ≤ lam₀⁻¹ → ‖G s‖ ≤ W₀) →
      (∀ y : ℝ, 0 < y → F y = κ₀ * (Complex.exp (a' * ((lam * y : ℝ) : ℂ)) * G (lam * y))) →
      (∀ i k, ‖∑ i₀ : Fin n, ∑ m : Fin J, L i k i₀ m * c i₀ m‖ ≤
        Ω' * ((n : ℝ) * Bc' * Real.exp aB *
          (∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re))) *
          ((J : ℝ) * (1 + |Real.log lam₀|) ^ J * 2 ^ J))) ∧
      ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖F y - ∑ i : Fin n, ∑ k : Fin J, (∑ i₀ : Fin n, ∑ m : Fin J, L i k i₀ m * c i₀ m) *
            ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (k : ℕ))‖ ≤
          max (Ω' * (Real.exp aB * C₁' +
              (aB ^ Kd / (Kd.factorial : ℝ) * 2 * Bc') * ∑ _i : Fin n, ∑ j : Fin J, ((j : ℝ) + 1) ^ (j : ℕ) +
              (Bc' * Real.exp aB) * ∑ _i : Fin n, ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ)) *
              max (lam₀ ^ (ρ + δ)) (lam₀ ^ (-(ρ + δ))))
            ((Ω' * W₀ + Ω' * ((n : ℝ) * Bc' * Real.exp aB *
                (∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re))) *
                ((J : ℝ) * (1 + |Real.log lam₀|) ^ J * 2 ^ J)) *
              ∑ i₁ : Fin n, ∑ j : Fin J, max (lam₀ ^ (e i₁).re) 1 * |Real.log lam₀| ^ (j : ℕ)) /
              min (lam₀ ^ (ρ + δ)) 1) * y ^ (ρ + δ) := by p2m_exact_reverting @_root_.P2MW.S_RegularSingular_exists_transferMatrix_expLogExpansion_rescale_expTwist.solution
