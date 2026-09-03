import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum

set_option autoImplicit false

open scoped MatrixGroups ModularForm

universe u in

theorem ModularCurve.exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum (M : ℕ) [NeZero M] :
    ∃ (B : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 2)
      (D : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 4)
      (b d : ZMod M → PowerSeries ℤ),
      (∀ c : ZMod M, ModularCurve.IsIntegralQExp (B c) (b c)) ∧
      (∀ c : ZMod M, ModularCurve.IsIntegralQExp (D c) (d c)) ∧
      (∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(B c) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ = ⇑(B (c * ((γ 0 0 : ℤ) : ZMod M))) ∧
        (⇑(D c) : UpperHalfPlane → ℂ) ∣[(4 : ℤ)] γ = ⇑(D (c * ((γ 0 0 : ℤ) : ZMod M)))) ∧
      ∀ (K : Type u) [Field K] (ζ : K), IsPrimitiveRoot ζ M → ∀ s : ZMod M, s ≠ 0 →
        (M : LaurentSeries K) ^ 3 * (1 + 12 * (ModularCurve.toricPoint K 1 (ζ ^ s.val)).1) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • ModularCurve.intSeriesC K (b c) ∧
        (M : LaurentSeries K) ^ 5 *
            ((ModularCurve.toricPoint K 1 (ζ ^ s.val)).1 +
                6 * (ModularCurve.toricPoint K 1 (ζ ^ s.val)).1 ^ 2 +
              2 * (ModularCurve.tateLaurent K).a₄) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • ModularCurve.intSeriesC K (d c) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum.solution
