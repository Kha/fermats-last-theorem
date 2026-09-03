import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_bilinForm_apply_eq_zero_of_inertia_cyclotomic
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one

set_option autoImplicit false
open scoped MatrixGroups

theorem ModularCurve.bilinForm_apply_eq_zero_of_inertia_cyclotomic
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (b : LinearMap.BilinForm (ZMod p) ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p))
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
      ∀ (x y x' y' : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
        (x' : ModularCurve.JH M H) = ModularCurve.diamondHBar M H (ZMod.unitOfCoprime c hc) (σ • (x : ModularCurve.JH M H)) →
        (y' : ModularCurve.JH M H) = σ • (y : ModularCurve.JH M H) →
          b x' y' = (c : ZMod p) • b x y)
    (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) (hx : (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ, (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • (x : ModularCurve.JH M H) = c • (x : ModularCurve.JH M H))) (hy : (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ, (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • (y : ModularCurve.JH M H) = c • (y : ModularCurve.JH M H))) :
    b x y = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_bilinForm_apply_eq_zero_of_inertia_cyclotomic.solution
