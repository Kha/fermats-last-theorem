import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_PowerSeries_FormalHeckeOperators
import P2M.Util
import P2M.Sol.S_PowerSeries_coeff_heckeT_pow_sub_mem_span
set_option autoImplicit false

theorem PowerSeries.coeff_heckeT_pow_sub_mem_span (p : ℕ) [Fact p.Prime] {N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (a : ℕ → integralClosure ℤ ℂ) (ha : ∀ n : ℕ, (a n : ℂ) = ModularFormClass.qCoeff f n)
    (j k : ℕ) (hk : 2 ≤ k) (hk2 : (p - 1 : ℕ) ∣ k - 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.heckeT ℓ k (PowerSeries.mk fun m => a m ^ p ^ j))
      - a ℓ ^ p ^ j * a n ^ p ^ j ∈ Ideal.span {(p : integralClosure ℤ ℂ)} := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_coeff_heckeT_pow_sub_mem_span.solution
