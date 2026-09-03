import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import P2M.Util
import P2M.Sol.S_Module_length_quotient_le_of_inertia_leibniz_family

theorem Module.length_quotient_le_of_inertia_leibniz_family
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {G : Type} [Group G] (Isub : Subgroup G) (σ γ : G) (hγI : γ ∈ Isub) (p q m : ℕ)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hdivI : ∀ τ ∈ Isub, ∃ w ∈ Isub, w ^ (p ^ m) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (hgen : ∀ τ ∈ Isub, ∃ (j : ℕ) (x w : G), x ∈ Isub ∧ w ∈ Isub ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m))
    (Fb : G → Matrix (Fin 2) (Fin 2) (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m))
    (hFmul : ∀ g h : G, Fb (g * h) = Fb g * Fb h) (hF1 : Fb 1 = 1)
    (hFI : ∀ τ ∈ Isub, Fb τ 1 0 = 0 ∧ Fb τ 0 0 = 1 ∧ Fb τ 1 1 = 1)
    (hFσ : Fb σ 1 0 = 0 ∧ Fb σ 0 0 = (q : 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) * Fb σ 1 1)
    {H : Type} [AddCommGroup H] [Module 𝒪 H]
    (Λ : H →ₗ[𝒪] (G → Matrix (Fin 2) (Fin 2) (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m)))
    (hLeib : ∀ (φ : H) (g h : G), Λ φ (g * h) = Fb g * Λ φ h + Λ φ g * Fb h)
    (K : Submodule 𝒪 H) (hK : ∀ φ : H, (∀ τ ∈ Isub, Λ φ τ 1 0 = 0) → φ ∈ K) :
    Module.length 𝒪 (H ⧸ K) ≤ Module.length 𝒪 (𝒪 ⧸ Ideal.span {(q : 𝒪) ^ 2 - 1}) := by p2m_exact_reverting @_root_.P2MW.S_Module_length_quotient_le_of_inertia_leibniz_family.solution
