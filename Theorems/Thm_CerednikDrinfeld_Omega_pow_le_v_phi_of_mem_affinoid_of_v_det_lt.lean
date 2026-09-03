import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_pow_le_v_phi_of_mem_affinoid_of_v_det_lt

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.pow_le_v_phi_of_mem_affinoid_of_v_det_lt
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) (n : ℕ) {b z : K} (hb : b ∈ affinoid ϖ n) (hz : z ∈ affinoid ϖ n)
    (g : Matrix (Fin 2) (Fin 2) K₀)
    (hle : ∀ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) ≤ 1)
    (hone : ∃ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) = 1)
    (hdet : Valued.v (algebraMap K₀ K g.det) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (6 * n)) :
    Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (4 * n) ≤
      Valued.v (z * (algebraMap K₀ K (g 1 0) * b + algebraMap K₀ K (g 1 1)) -
        (algebraMap K₀ K (g 0 0) * b + algebraMap K₀ K (g 0 1))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_pow_le_v_phi_of_mem_affinoid_of_v_det_lt.solution
