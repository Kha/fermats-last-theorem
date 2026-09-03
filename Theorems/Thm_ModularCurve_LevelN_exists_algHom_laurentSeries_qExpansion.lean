import Mathlib
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.LevelN.exists_algHom_laurentSeries_qExpansion (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    ∃ E : K →ₐ[ℂ] LaurentSeries ℂ,
      E (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) =
          ModularCurve.qExpand ℂ N (ModularCurve.jqModC ℂ) ∧
      ∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N) (m : ℕ),
        UpperHalfPlane.IsBoundedAtImInfty (F * ModularForm.discriminant ^ m) →
        E (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) *
            HahnSeries.ofPowerSeries ℤ ℂ
              (UpperHalfPlane.qExpansion N (ModularForm.discriminant : UpperHalfPlane → ℂ)) ^ m =
          HahnSeries.ofPowerSeries ℤ ℂ
            (UpperHalfPlane.qExpansion N (F * ModularForm.discriminant ^ m)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.solution
