import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq

set_option autoImplicit false

open scoped TensorProduct

theorem Ideal.eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq
    {W W' : Type*} [CommRing W] [CommRing W'] [Algebra W W']
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
    (hinv : ∀ w' : W', (∀ γ : Γ, γ • w' = w') → w' ∈ Set.range (algebraMap W W'))
    {n : ℕ} (x y : Fin n → W') (hxy : ∀ γ : Γ, ∑ i, x i * γ • y i = if γ = 1 then 1 else 0)
    (S : Type*) [CommRing S] [Algebra W S]
    (J' : Ideal (S ⊗[W] W'))
    (hstab : ∀ γ : Γ, J'.map (Algebra.TensorProduct.map (AlgHom.id S S) (MulSemiringAction.toAlgHom W W' γ)) = J') :
    J' = (J'.comap (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[W] W')).map
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[W] W') := by p2m_exact_reverting @_root_.P2MW.S_Ideal_eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq.solution
