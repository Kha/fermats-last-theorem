import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_exists_mem_inertiaInvariants_nsmul_eq_zero_sub_extendsToPlace

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_mem_inertiaInvariants_nsmul_eq_zero_sub_extendsToPlace
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) (hmp : m.Coprime p)
    (y : JZero (N₀ * p)) (hy : y ∈ inertiaInvariants A (N₀ * p))
    (hmy : ExtendsToPlace A Λ.σA (O.pts (m • y))) :
    ∃ x : JZero (N₀ * p), x ∈ inertiaInvariants A (N₀ * p) ∧ m • x = 0 ∧
      ExtendsToPlace A Λ.σA (O.pts (y - x)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_mem_inertiaInvariants_nsmul_eq_zero_sub_extendsToPlace.solution
