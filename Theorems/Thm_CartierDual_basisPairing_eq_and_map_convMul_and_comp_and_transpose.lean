import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_CartierDual_basisPairing_eq_and_map_convMul_and_comp_and_transpose

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.basisPairing_eq_and_map_convMul_and_comp_and_transpose
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] [Module.Free R A]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R A)
    (L : Type*) [CommRing L] [Algebra R L] :

    (∀ {ι' : Type*} [Fintype ι'] (b' : Module.Basis ι' R A)
        (f : A →ₗ[R] L) (Ψ : Module.Dual R A →ₗ[R] L),
        ∑ i, f (b i) * Ψ (b.coord i) = ∑ j, f (b' j) * Ψ (b'.coord j)) ∧

    (∀ {L' : Type*} [CommRing L'] [Algebra R L'] (φ : L →ₐ[R] L')
        (f : A →ₗ[R] L) (Ψ : Module.Dual R A →ₗ[R] L),
        φ (∑ i, f (b i) * Ψ (b.coord i)) = ∑ i, φ (f (b i)) * φ (Ψ (b.coord i))) ∧

    (∀ {A' : Type*} [AddCommGroup A'] [Module R A'] {ι' : Type*} [Fintype ι'] (b' : Module.Basis ι' R A')
        (t : A' →ₗ[R] A) (_ : Function.Surjective t) (N : A' →ₗ[R] A')
        (u : Module.Dual R A' →ₗ[R] Module.Dual R A) (_ : ∀ (φ' : Module.Dual R A') (a' : A'), u φ' (t a') = φ' (N a'))
        (f : A →ₗ[R] L) (F : A' →ₗ[R] L) (_ : ∀ a' : A', F (N a') = f (t a'))
        (Ψ : Module.Dual R A →ₗ[R] L),
        ∑ k, F (b' k) * Ψ (u (b'.coord k)) = ∑ i, f (b i) * Ψ (b.coord i)) ∧

    (∀ (f g : WithConv (A →ₐ[R] L)) (ψ : CartierDual R A →ₐ[R] L),
        ∑ i, (f * g) (b i) * ψ (CartierDual.ofDual R A (b.coord i)) =
          (∑ i, f (b i) * ψ (CartierDual.ofDual R A (b.coord i))) *
            ∑ i, g (b i) * ψ (CartierDual.ofDual R A (b.coord i))) ∧

    (∀ (f : A →ₐ[R] L) (ψ ψ' : WithConv (CartierDual R A →ₐ[R] L)),
        ∑ i, f (b i) * (ψ * ψ') (CartierDual.ofDual R A (b.coord i)) =
          (∑ i, f (b i) * ψ (CartierDual.ofDual R A (b.coord i))) *
            ∑ i, f (b i) * ψ' (CartierDual.ofDual R A (b.coord i))) ∧

    (∀ ψ : CartierDual R A →ₐ[R] L,
        ∑ i, (1 : WithConv (A →ₐ[R] L)) (b i) * ψ (CartierDual.ofDual R A (b.coord i)) = 1) ∧
    (∀ f : A →ₐ[R] L,
        ∑ i, f (b i) * (1 : WithConv (CartierDual R A →ₐ[R] L)) (CartierDual.ofDual R A (b.coord i)) = 1) ∧

    (∀ (f : WithConv (A →ₐ[R] L)) (ψ : CartierDual R A →ₐ[R] L) (n : ℕ),
        ∑ i, (f ^ n) (b i) * ψ (CartierDual.ofDual R A (b.coord i)) =
          (∑ i, f (b i) * ψ (CartierDual.ofDual R A (b.coord i))) ^ n) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_basisPairing_eq_and_map_convMul_and_comp_and_transpose.solution
