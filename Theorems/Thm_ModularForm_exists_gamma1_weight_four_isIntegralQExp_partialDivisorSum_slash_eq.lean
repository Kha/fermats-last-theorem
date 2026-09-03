import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_ModularForm_exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem ModularForm.exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq
    (M : ℕ) [NeZero M] (hM : 3 ≤ M) :
    ∃ R : (ZMod M)ˣ → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 4,
      (∀ c : (ZMod M)ˣ, ModularCurve.IsIntegralQExp (R c)
        (PowerSeries.mk fun n : ℕ => if n = 0 then 0 else
          ∑ d ∈ n.divisors,
            if ((n / d : ℕ) : ZMod M) = (c : ZMod M) ∨ ((n / d : ℕ) : ZMod M) = -(c : ZMod M)
            then (d : ℤ) ^ 3 else 0)) ∧
      (∀ (c : (ZMod M)ˣ) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M),
        ((⇑(R c) : UpperHalfPlane → ℂ) ∣[(4 : ℤ)] (γ : GL (Fin 2) ℝ)) =
          ⇑(R (c * (CohCarrier.gamma0Units M ⟨γ, hγ⟩)⁻¹))) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq.solution
