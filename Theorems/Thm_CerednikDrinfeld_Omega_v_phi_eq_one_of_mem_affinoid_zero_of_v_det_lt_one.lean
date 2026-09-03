import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_v_phi_eq_one_of_mem_affinoid_zero_of_v_det_lt_one

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega~pow_le_v_phi_of_mem_affinoid_of_v_det_lt"

theorem CerednikDrinfeld.Omega.v_phi_eq_one_of_mem_affinoid_zero_of_v_det_lt_one
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ₁ : PseudoUniformizer K₀ K) {w u : K} (hw : w ∈ affinoid ϖ₁ 0) (hu : u ∈ affinoid ϖ₁ 0)
    (m : Matrix (Fin 2) (Fin 2) K₀)
    (hle : ∀ i j : Fin 2, Valued.v (algebraMap K₀ K (m i j)) ≤ 1)
    (hone : ∃ i j : Fin 2, Valued.v (algebraMap K₀ K (m i j)) = 1)
    (hdet : Valued.v (algebraMap K₀ K m.det) < 1) :
    Valued.v (w * (algebraMap K₀ K (m 1 0) * u + algebraMap K₀ K (m 1 1)) -
      (algebraMap K₀ K (m 0 0) * u + algebraMap K₀ K (m 0 1))) = 1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_v_phi_eq_one_of_mem_affinoid_zero_of_v_det_lt_one.solution
