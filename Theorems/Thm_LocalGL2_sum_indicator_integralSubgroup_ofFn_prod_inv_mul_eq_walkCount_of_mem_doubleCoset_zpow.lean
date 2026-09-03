import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import P2M.Util
import P2M.Sol.S_LocalGL2_sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow

set_option autoImplicit false

theorem LocalGL2.sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {ι : Type*} [Fintype ι] (r : ι → GL (Fin 2) K)
    (hr : HeckeIntegralSeam.IsHeckeCosetSystem (LocalGL2.integralSubgroup R K) (LocalGL2.diagPi ϖ hϖ0) r)
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Nat.card (R ⧸ Ideal.span {ϖ}) * W k (d + 2))
    (k : ℕ) (a b : ℤ) (y : GL (Fin 2) K)
    (hy : y ∈ HeckePair.doubleCoset (LocalGL2.integralSubgroup R K)
      (LocalGL2.diagPi ϖ hϖ0 ^ a * LocalGL2.localRepInf ϖ hϖ0 ^ b)) :
    ∑ w : Fin k → ι, (LocalGL2.integralSubgroup R K : Set (GL (Fin 2) K)).indicator (fun _ => (1 : ℕ))
        (((List.ofFn fun j => r (w j)).prod)⁻¹ * y) =
      if a + b = k then W k (a - b).natAbs else 0 := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow.solution
