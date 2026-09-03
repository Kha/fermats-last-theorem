import Mathlib
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_MvPowerSeries_subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv

set_option autoImplicit false

open MvPowerSeries
theorem MvPowerSeries.subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv
    {R : Type} [CommRing R] {σ : Type} [Fintype σ] {τ : Type} [Fintype τ] {κ : Type} [Fintype κ]
    (j : κ → R) (hj : ∀ k k', j k * j k' = 0)
    (f : MvPowerSeries σ R)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, MvPowerSeries.constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) :
    MvPowerSeries.subst (fun i => A i + ∑ k, j k • B i k) f =
      MvPowerSeries.subst A f + ∑ k, j k • ∑ i, B i k * MvPowerSeries.subst A (MvPowerSeries.pderivLin i f) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv.solution
