import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_exists_addMonoidHom_finPts_eq_ptsSp_symm_fibreMap_abqFibre

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_addMonoidHom_finPts_eq_ptsSp_symm_fibreMap_abqFibre
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) (m : ℕ) :
    ∃ ν : ↥(O.finPts m) →+ JZeroC (ResidueField ↥A) N₀,
      (∀ (x : ↥(O.finPts m)) (s : SchemeHomOver Λ.σA O.g),
        (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
          ν x = Λ.ptsSp.symm (fibreMap (O.abqFibre i)
            (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s))) ∧
      (∀ x : ↥(O.finPts m), m • ν x = 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_addMonoidHom_finPts_eq_ptsSp_symm_fibreMap_abqFibre.solution
