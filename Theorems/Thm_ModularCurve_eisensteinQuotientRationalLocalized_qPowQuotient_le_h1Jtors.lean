import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import P2M.Util
import P2M.Sol.S_ModularCurve_eisensteinQuotientRationalLocalized_qPowQuotient_le_h1Jtors

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.eisensteinQuotientRationalLocalized_qPowQuotient_le_h1Jtors (p : ℕ)
    [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) (q : ℕ) [Fact q.Prime]
    (hfgc : letI := heckeModuleBar p
      AddGroup.FG ↥(AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p))))
    (R : ∀ m : ℕ, JKummerRow q m (eisensteinQuotientRationalLocalized p q))
    (hfinH : ∀ m : ℕ, letI := (R m).instH1Jtors; Finite (R m).H1Jtors) :
    ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ m : ℕ,
      letI := (R m).instH1Jtors
      (@AddMonoidHom.range (eisensteinQuotientRationalLocalized p q) _
          (eisensteinQuotientRationalLocalized p q) _
          ((q : ℤ) ^ m • AddMonoidHom.id (eisensteinQuotientRationalLocalized p q))).index ≤ c₀ * Nat.card (R m).H1Jtors := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisensteinQuotientRationalLocalized_qPowQuotient_le_h1Jtors.solution
