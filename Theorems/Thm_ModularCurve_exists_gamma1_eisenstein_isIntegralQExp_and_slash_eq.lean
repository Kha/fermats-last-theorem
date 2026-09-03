import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq (M : ℕ) [NeZero M]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ G : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ c : ZMod M, c ≠ 0 →
        ModularCurve.IsIntegralQExp (G c)
          (PowerSeries.mk fun n : ℕ =>
            (∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = c, (m : ℤ) ^ (k - 1)) +
              (-1) ^ k * ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = -c, (m : ℤ) ^ (k - 1))) ∧
      ∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        ((⇑(G c) : UpperHalfPlane → ℂ) ∣[(k : ℤ)] γ) =
          (⇑(G (c * ((γ 0 0 : ℤ) : ZMod M))) : UpperHalfPlane → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq.solution
