import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_forall_fixed_mem_range

set_option autoImplicit false
open scoped TensorProduct

theorem HopfAlgebra.exists_bialgHom_forall_comp_eq_of_equivariant_of_forall_fixed_mem_range
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D : Subgroup (L ≃ₐ[K] L))
    (hfix : ∀ x : L, (∀ σ ∈ D, σ x = x) → x ∈ Set.range (algebraMap K L))
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Module.Finite K A]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (A →ₐ[K] L) → L))
        (Pi.algHom K _ fun ν : WithConv (A →ₐ[K] L) => (WithConv.ofConv ν : A →ₐ[K] L))
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (WithConv (A →ₐ[K] L) → L)))
    (φ : WithConv (A →ₐ[K] L) →* WithConv (A →ₐ[K] L))
    (hφ : ∀ σ : L ≃ₐ[K] L, σ ∈ D → ∀ ν ν' : WithConv (A →ₐ[K] L),
        (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
        ∀ a : A, WithConv.ofConv (φ ν') a = σ (WithConv.ofConv (φ ν) a)) :
    ∃ u : A →ₐc[K] A, ∀ ν : WithConv (A →ₐ[K] L),
      WithConv.toConv ((WithConv.ofConv ν).comp (u : A →ₐ[K] A)) = φ ν := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_forall_fixed_mem_range.solution
