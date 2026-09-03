import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import P2M.Util
import P2M.Sol.S_ModularCurve_eisensteinQuotientRationalLocalized_eisensteinPrimary_stabilizes

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.eisensteinQuotientRationalLocalized_eisensteinPrimary_stabilizes (p : ℕ)
    [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) (q : ℕ) [Fact q.Prime]
    (hfgc : letI := heckeModuleBar p
      AddGroup.FG ↥(AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p))))
    (R : ∀ m : ℕ, JKummerRow q m (eisensteinQuotientRationalLocalized p q))
    (hA1 : ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ m : ℕ,
      letI := (R m).instH1Jtors
      (@AddMonoidHom.range (eisensteinQuotientRationalLocalized p q) _
          (eisensteinQuotientRationalLocalized p q) _
          ((q : ℤ) ^ m • AddMonoidHom.id (eisensteinQuotientRationalLocalized p q))).index ≤ c₀ * Nat.card (R m).H1Jtors)
    (hA2 : ∃ Kb : ℕ, ∀ m : ℕ,
      letI := (R m).instH1Jtors
      Nat.card (R m).H1Jtors ≤ Kb) :
    letI := heckeModuleBar p
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (eisensteinMaximalIdeal p q ^ m •
          Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))) =
        (eisensteinMaximalIdeal p q ^ m₀ •
          Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisensteinQuotientRationalLocalized_eisensteinPrimary_stabilizes.solution
