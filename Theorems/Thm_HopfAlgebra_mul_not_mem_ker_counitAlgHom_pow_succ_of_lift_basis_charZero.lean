import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero

theorem HopfAlgebra.mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A]
    {ι : Type*} [Fintype ι] {ξ : ι → A}
    (hξI : ∀ i, ξ i ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom)
    (hξli : LinearIndependent K
      (fun i ↦ Ideal.Quotient.mk ((RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) (ξ i)))
    (hξspan : ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom,
      ∃ c : ι → K, a - ∑ i, c i • ξ i ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2)
    {m n : ℕ} {x y : A}
    (hxm : x ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ m)
    (hxm' : x ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (m + 1))
    (hyn : y ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ n)
    (hyn' : y ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (n + 1)) :
    x * y ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (m + n + 1) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero.solution
