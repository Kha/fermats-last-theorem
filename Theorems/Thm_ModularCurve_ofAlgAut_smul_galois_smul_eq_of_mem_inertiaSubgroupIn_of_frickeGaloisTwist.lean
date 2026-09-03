import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_ofAlgAut_smul_galois_smul_eq_of_mem_inertiaSubgroupIn_of_frickeGaloisTwist
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve~diamondHBar_apply_eq_self_of_mem"

theorem ModularCurve.ofAlgAut_smul_galois_smul_eq_of_mem_inertiaSubgroupIn_of_frickeGaloisTwist
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (w : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] ModularCurve.xHFunctionFieldBar M H)

    (hw4 : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ x : ModularCurve.JH M H,
          AlgebraicCurve.SemilinearAut.ofAlgAut w • (σ • x)
            = σ • ModularCurve.diamondHBar M H (ZMod.unitOfCoprime c hc) (AlgebraicCurve.SemilinearAut.ofAlgAut w • x))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ Pl.inertiaSubgroupIn ℚ) (x : ModularCurve.JH M H) :
    AlgebraicCurve.SemilinearAut.ofAlgAut w • (σ • x) = σ • (AlgebraicCurve.SemilinearAut.ofAlgAut w • x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ofAlgAut_smul_galois_smul_eq_of_mem_inertiaSubgroupIn_of_frickeGaloisTwist.solution
