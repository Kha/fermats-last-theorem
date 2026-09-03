import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_JZeroTorsionFinite
import Definitions.Def_ModularCurve_EisensteinIdeal
import Mathlib.Algebra.Ring.Action.Submonoid
import P2M.Util
import P2M.Sol.S_ModularCurve_eisensteinQuotientRational_isTorsion_heckeModuleBar_of_perPrimeFinite
open ModularCurve AlgebraicCurve
theorem ModularCurve.eisensteinQuotientRational_isTorsion_heckeModuleBar_of_perPrimeFinite
    (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p)
    (hfgc : letI := heckeModuleBar p
      AddGroup.FG ↥(AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p))))
    (hA : letI := heckeModuleBar p
      ∀ q : ℕ, q.Prime → q ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12 →
        ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
          (eisensteinMaximalIdeal p q ^ m •
              Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))) =
            (eisensteinMaximalIdeal p q ^ m₀ •
              Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))))
    (hB : letI := heckeModuleBar p
      ∀ z ∈ AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)),
        (∀ q : ℕ, q.Prime →
            ∃ s : HeckeAlg, s ∉ eisensteinMaximalIdeal p q ∧ IsOfFinAddOrder (s • z)) →
          IsOfFinAddOrder z)
    (hC : ∃ t ∈ eisensteinIdeal p, ∃ k : ℤ, k ≠ 0 ∧
        k.natAbs ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12 ∧
        heckeEvalBar hcomm t = k • (1 : Module.End ℤ (JZero p))) :
    letI := heckeModuleBar p
    ∀ z ∈ eisensteinQuotientRational p (heckeModuleBar p), ∃ n : ℕ, 0 < n ∧ n • z = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisensteinQuotientRational_isTorsion_heckeModuleBar_of_perPrimeFinite.solution
