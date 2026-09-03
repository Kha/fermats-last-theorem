import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_coaction_eq_tmul_one_add_one_tmul_of_comul_eq_of_faithfullyFlat

set_option autoImplicit false

open TensorProduct

universe u

theorem HopfAlgebra.exists_coaction_eq_tmul_one_add_one_tmul_of_comul_eq_of_faithfullyFlat
    {K : Type u} [Field K] {R S H : Type u} [CommRing R] [CommRing S] [CommRing H]
    [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S] [Module.FaithfullyFlat R S]
    [HopfAlgebra K H]
    (ρ : S →ₐ[K] S ⊗[K] H)
    (hρR : ∀ r : R, ρ (algebraMap R S r) = algebraMap R S r ⊗ₜ[K] (1 : H))
    (hcounit : ∀ s : S,
      (Algebra.TensorProduct.rid K K S) (Algebra.TensorProduct.map (AlgHom.id K S) (Bialgebra.counitAlgHom K H) (ρ s)) = s)
    (hcoassoc : ∀ s : S,
      (Algebra.TensorProduct.assoc K K K S H H) (Algebra.TensorProduct.map ρ (AlgHom.id K H) (ρ s)) =
        Algebra.TensorProduct.map (AlgHom.id K S) (Bialgebra.comulAlgHom K H) (ρ s))
    (σ : S ⊗[R] S →+* S ⊗[K] H) (hσ : Function.Bijective σ)
    (hσ_left : ∀ s : S, σ (s ⊗ₜ[R] 1) = s ⊗ₜ[K] 1) (hσ_right : ∀ s : S, σ (1 ⊗ₜ[R] s) = ρ s)
    (h : H) (hh : Coalgebra.comul (R := K) h = h ⊗ₜ[K] 1 + 1 ⊗ₜ[K] h) :
    (∃ s : S, ρ s = s ⊗ₜ[K] 1 + (1 : S) ⊗ₜ[K] h) ∧
      (∀ s : S, ρ s = s ⊗ₜ[K] 1 → s ∈ Set.range (algebraMap R S)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_coaction_eq_tmul_one_add_one_tmul_of_comul_eq_of_faithfullyFlat.solution
