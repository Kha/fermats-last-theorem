import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_exists_gradedAlgebra_isBaseChange_of_bijective_of_decompose_mem

set_option autoImplicit false

universe u

open TensorProduct

theorem Subalgebra.exists_gradedAlgebra_isBaseChange_of_bijective_of_decompose_mem
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    (A' : Type u) [CommRing A'] [Algebra S A'] [Algebra S' A'] [IsScalarTower S S' A']
    (𝒜' : ℕ → Submodule S' A') [GradedAlgebra 𝒜']
    (A : Subalgebra S A')
    (hbij : Function.Bijective
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val (fun _ _ => Commute.all _ _)))
    (hhom : ∀ a ∈ A, ∀ n : ℕ, (DirectSum.decompose 𝒜' a n : A') ∈ A) :
    ∃ (𝒜 : ℕ → Submodule S A) (_ : GradedAlgebra 𝒜) (h𝒜 : ∀ n, ∀ a ∈ 𝒜 n, A.val a ∈ 𝒜' n),
      (∀ (n : ℕ) (a : A), (a : A') ∈ 𝒜' n → a ∈ 𝒜 n) ∧
      (∀ n, IsBaseChange S' ((A.val.toLinearMap.restrict (p := 𝒜 n) (q := (𝒜' n).restrictScalars S) (h𝒜 n))
        : 𝒜 n →ₗ[S] (𝒜' n).restrictScalars S)) ∧
      HomogeneousIdeal.irrelevant 𝒜' ≤
        (HomogeneousIdeal.irrelevant 𝒜).map ({ A.val.toRingHom with map_mem := fun h => h𝒜 _ _ h } : 𝒜 →+*ᵍ 𝒜') := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_exists_gradedAlgebra_isBaseChange_of_bijective_of_decompose_mem.solution
