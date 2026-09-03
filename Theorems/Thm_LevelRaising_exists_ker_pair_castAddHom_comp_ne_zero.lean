import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Prod
import P2M.Util
import P2M.Sol.S_LevelRaising_exists_ker_pair_castAddHom_comp_ne_zero

set_option autoImplicit false
theorem LevelRaising.exists_ker_pair_castAddHom_comp_ne_zero
    {A₁ A₀ : Type*} [AddZeroClass A₁] [AddZeroClass A₀]
    (par₁ : Submodule ℤ (A₁ →+ ℤ)) (par₀ : Submodule ℤ (A₀ →+ ℤ))
    {p : ℕ} [Fact p.Prime]
    (T₁ : (ℓ : ℕ) → [NeZero ℓ] → ((A₁ →+ ℤ) →+ (A₁ →+ ℤ)))
    (hT₁par : ∀ (ℓ : ℕ) [NeZero ℓ], ∀ x ∈ par₁, T₁ ℓ x ∈ par₁)
    (ℓ₀ : ℕ) [NeZero ℓ₀]
    (T₀ : (A₀ →+ ℤ) →+ (A₀ →+ ℤ)) (hT₀par : ∀ x ∈ par₀, T₀ x ∈ par₀)
    (β₀ β₁ : (A₁ →+ ℤ) →+ (A₀ →+ ℤ))
    (hβpar₀ : ∀ x ∈ par₁, β₀ x ∈ par₀) (hβpar₁ : ∀ x ∈ par₁, β₁ x ∈ par₀)
    (hβT : (LinearMap.prod (β₀.toIntLinearMap.restrict hβpar₀)
          (β₁.toIntLinearMap.restrict hβpar₁)) ∘ₗ
        ((T₁ ℓ₀).toIntLinearMap.restrict (hT₁par ℓ₀))
      = (LinearMap.prodMap (T₀.toIntLinearMap.restrict hT₀par)
          (T₀.toIntLinearMap.restrict hT₀par)) ∘ₗ
        (LinearMap.prod (β₀.toIntLinearMap.restrict hβpar₀)
          (β₁.toIntLinearMap.restrict hβpar₁)))
    (a : ℕ → ℤ) (S : ℕ → Prop)
    (hcomm : ∀ (ℓ : ℕ) [NeZero ℓ], S ℓ → ∀ x : A₁ →+ ℤ, T₁ ℓ (T₁ ℓ₀ x) = T₁ ℓ₀ (T₁ ℓ x))
    (hloc : ∀ h : ↥par₀ × ↥par₀, ∃ s : Polynomial ℤ, ((s.eval (a ℓ₀) : ℤ) : ZMod p) ≠ 0 ∧
      ∃ x : ↥par₁,
        (Polynomial.aeval (LinearMap.prodMap (T₀.toIntLinearMap.restrict hT₀par)
          (T₀.toIntLinearMap.restrict hT₀par)) s) h
        = (LinearMap.prod (β₀.toIntLinearMap.restrict hβpar₀)
            (β₁.toIntLinearMap.restrict hβpar₁)) x)
    (hsat₀ : ∀ δ : A₀ →+ ℤ, (p : ℤ) • δ ∈ par₀ → δ ∈ par₀)
    (g : A₁ →+ ℤ) (hgpar : g ∈ par₁) (hgne : (Int.castAddHom (ZMod p)).comp g ≠ 0)
    (hgβ₀ : ∃ δ₀ : A₀ →+ ℤ, β₀ g = (p : ℤ) • δ₀)
    (hgβ₁ : ∃ δ₁ : A₀ →+ ℤ, β₁ g = (p : ℤ) • δ₁)
    (hg₀ : ∃ ψ : A₁ →+ ℤ, T₁ ℓ₀ g - a ℓ₀ • g = (p : ℤ) • ψ)
    (hgeig : ∀ (ℓ : ℕ) [NeZero ℓ], S ℓ → ∃ ψ : A₁ →+ ℤ, T₁ ℓ g - a ℓ • g = (p : ℤ) • ψ) :
    ∃ H : A₁ →+ ℤ, H ∈ par₁ ∧ β₀ H = 0 ∧ β₁ H = 0 ∧
      (Int.castAddHom (ZMod p)).comp H ≠ 0 ∧
      ∀ (ℓ : ℕ) [NeZero ℓ], S ℓ →
        ∃ ψ : A₁ →+ ℤ, T₁ ℓ H - a ℓ • H = (p : ℤ) • ψ := by p2m_exact_reverting @_root_.P2MW.S_LevelRaising_exists_ker_pair_castAddHom_comp_ne_zero.solution
