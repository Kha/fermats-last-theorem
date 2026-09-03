import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Operations
import P2M.Util
import P2M.Sol.S_TW12_exists_groupAlgebra_basis_of_descent
set_option autoImplicit false
theorem TW12.exists_groupAlgebra_basis_of_descent {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {p : ℕ} [Fact p.Prime] (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (Δ : Type) [CommGroup Δ] [Fintype Δ]
    (hΔ : ∀ g : Δ, ∃ n : ℕ, g ^ (p ^ n) = 1)
    (M : Type) [AddCommGroup M] [Module (MonoidAlgebra 𝒪 Δ) M]
    [Module 𝒪 M] [IsScalarTower 𝒪 (MonoidAlgebra 𝒪 Δ) M]
    (d : ℕ)
    (B : Fin (d * Fintype.card Δ) → M)
    (hBspan : ∀ x : M, ∃ a : Fin (d * Fintype.card Δ) → 𝒪, x = ∑ i, a i • B i)
    (hBrel : ∀ a : Fin (d * Fintype.card Δ) → 𝒪,
      ∑ i, a i • B i = 0 ↔ ∀ i, a i = 0)
    (M₀ : Type) [AddCommGroup M₀] [Module 𝒪 M₀]
    (lam : M →+ M₀)
    (hlam_smul : ∀ (a : 𝒪) (m : M), lam (a • m) = a • lam m)
    (hlam_surj : Function.Surjective lam)
    (hlam_ker : ∀ m : M, lam m = 0 ↔ m ∈
      (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ))) •
        (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M))
    (b₀ : Fin d → M₀)
    (hb₀span : ∀ x : M₀, ∃ a : Fin d → 𝒪, x = ∑ i, a i • b₀ i) :
    ∃ b : Fin d → M,
      (∀ x : M, ∃ c : Fin d → MonoidAlgebra 𝒪 Δ, x = ∑ i, c i • b i) ∧
      (∀ c : Fin d → MonoidAlgebra 𝒪 Δ, ∑ i, c i • b i = 0 ↔ ∀ i, c i = 0) := by p2m_exact_reverting @_root_.P2MW.S_TW12_exists_groupAlgebra_basis_of_descent.solution
