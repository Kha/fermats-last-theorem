import Mathlib
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.LevelN.exists_place_ord_neg_forall_smul_eq (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K]
    (hst : ∀ F ∈ ModularCurve.LevelN.ring N,
      (fun τ : UpperHalfPlane => F (ModularGroup.T⁻¹ • τ)) ∈ ModularCurve.LevelN.ring N) :
    ∃ W : AlgebraicCurve.Place ℂ K,
      W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) < 0 ∧
      ∀ φ : K ≃ₐ[ℂ] K,
        (∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N),
            φ (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) =
              algebraMap (ModularCurve.LevelN.ring N) K
                ⟨fun τ : UpperHalfPlane => F (ModularGroup.T⁻¹ • τ), hst F hF⟩) →
        AlgebraicCurve.SemilinearAut.ofAlgAut φ • W = W := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq.solution
