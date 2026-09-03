import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import P2M.Util
import P2M.Sol.S_Module_length_quotient_le_of_inertia_additive_family

theorem Module.length_quotient_le_of_inertia_additive_family
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {G : Type} [Group G] (Isub : Subgroup G) (σ γ : G) (hγI : γ ∈ Isub) (p q m : ℕ)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hdivI : ∀ τ ∈ Isub, ∃ w ∈ Isub, w ^ (p ^ m) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (hgen : ∀ τ ∈ Isub, ∃ (j : ℕ) (x w : G), x ∈ Isub ∧ w ∈ Isub ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m))
    (F F' : Matrix (Fin 2) (Fin 2) 𝒪) (hFF' : F * F' = 1) (a : 𝒪) (htr : F.trace = a)
    (hdet : F.det = (q : 𝒪)) (hq : IsUnit (q : 𝒪))
    {H : Type} [AddCommGroup H] [Module 𝒪 H]
    (Λ : H →ₗ[𝒪] (G → Matrix (Fin 2) (Fin 2) (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m)))
    (hadd : ∀ φ : H, ∀ x ∈ Isub, ∀ y ∈ Isub, Λ φ (x * y) = Λ φ x + Λ φ y)
    (hequiv : ∀ φ : H, ∀ τ ∈ Isub, Λ φ (σ * τ * σ⁻¹) =
      F.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪) ^ m)) * Λ φ τ *
        F'.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪) ^ m)))
    (htr0 : ∀ φ : H, ∀ τ ∈ Isub, Matrix.trace (Λ φ τ) = 0)
    (K : Submodule 𝒪 H) (hK : ∀ φ : H, (∀ τ ∈ Isub, Λ φ τ = 0) → φ ∈ K) :
    Module.length 𝒪 (H ⧸ K) ≤
      Module.length 𝒪 (𝒪 ⧸ Ideal.span {((q : 𝒪) - 1) * (a ^ 2 - ((q : 𝒪) + 1) ^ 2)}) := by p2m_exact_reverting @_root_.P2MW.S_Module_length_quotient_le_of_inertia_additive_family.solution
