import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import P2M.Util
import P2M.Sol.S_MonoidAlgebra_free_coinvariants_and_exists_linearEquiv_of_free_of_ker_eq

set_option autoImplicit false

theorem MonoidAlgebra.free_coinvariants_and_exists_linearEquiv_of_free_of_ker_eq
    {𝒪 : Type*} [CommRing 𝒪] [Nontrivial 𝒪]
    {Δ : Type*} [CommMonoid Δ]
    {R : Type*} [Ring R] [Algebra 𝒪 R] (ι : MonoidAlgebra 𝒪 Δ →ₐ[𝒪] R)
    {M : Type*} [AddCommGroup M] [Module R M] [Module (MonoidAlgebra 𝒪 Δ) M] [Module 𝒪 M]
    [IsScalarTower 𝒪 (MonoidAlgebra 𝒪 Δ) M] [Module.Free (MonoidAlgebra 𝒪 Δ) M]
    (hι : ∀ (c : MonoidAlgebra 𝒪 Δ) (m : M), c • m = ι c • m)
    {T₀ : Type*} [Ring T₀] [Algebra 𝒪 T₀] (ψ : R →ₐ[𝒪] T₀)
    {M₀ : Type*} [AddCommGroup M₀] [Module T₀ M₀] [Module 𝒪 M₀]
    (π : M →ₗ[𝒪] M₀) (hπ : Function.Surjective π)
    (hπψ : ∀ (x : R) (m : M), π (x • m) = ψ x • π m)
    (hker : ∀ m : M, π m = 0 ↔
      m ∈ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)) •
        (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M))) :
    Module.Free 𝒪 (M ⧸ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)) •
        (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M))) ∧
    Module.rank 𝒪 (M ⧸ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)) •
        (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M))) = Module.rank (MonoidAlgebra 𝒪 Δ) M ∧
    ∃ e : (M ⧸ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)) •
        (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M))) ≃ₗ[𝒪] M₀,
      (∀ m : M, e (Submodule.Quotient.mk m) = π m) ∧
      ∀ (x : R) (m : M),
        e (Submodule.Quotient.mk (x • m)) = ψ x • e (Submodule.Quotient.mk m) := by p2m_exact_reverting @_root_.P2MW.S_MonoidAlgebra_free_coinvariants_and_exists_linearEquiv_of_free_of_ker_eq.solution
