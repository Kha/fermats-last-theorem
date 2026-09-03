import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_comp_degeneracyHom_eq_degeneracyHom_comp

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.comp_degeneracyHom_eq_degeneracyHom_comp
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) (t t' : HeckeAlg)
    (φ : SchemeHomOver O.g O.g)
    (hφt : letI := heckeModuleBar (N₀ * p); ∀ x : JZero (N₀ * p), (O.pts (t • x)).1 = (O.pts x).1 ≫ φ.1)
    (φ' : SchemeHomOver Λ.f Λ.f)
    (hφ't : letI := heckeModuleBar N₀; ∀ x : JZero N₀, (Λ.pts (t' • x)).1 = (Λ.pts x).1 ≫ φ'.1)
    (hdeg : ∀ x : JZero (N₀ * p),
      degeneracyPushforwardPair N₀ p i (letI := heckeModuleBar (N₀ * p); t • x) =
        (letI := heckeModuleBar N₀; t' • degeneracyPushforwardPair N₀ p i x)) :
    φ.1 ≫ (O.degeneracyHom i).1 = (O.degeneracyHom i).1 ≫ φ'.1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_comp_degeneracyHom_eq_degeneracyHom_comp.solution
