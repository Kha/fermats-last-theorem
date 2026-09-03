import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul

set_option autoImplicit false

universe u

open scoped MatrixGroups

theorem ModularCurve.diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) :
    (∀ d d' : (ZMod N)ˣ,
        ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N (d * d')) =
          ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d) *
            ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d')) ∧
    (∀ d : (ZMod N)ˣ, d ∈ H' → ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d) = 1) ∧
    (∀ d d' : (ZMod N)ˣ, d * d'⁻¹ ∈ H' ⊔ Subgroup.zpowers (-1 : (ZMod N)ˣ) →
        ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d) =
          ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d')) ∧
    (∀ d : (ZMod N)ˣ,
        ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d) *
          ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹) = 1) ∧

    (∀ (X : Type u) [MulAction (AlgebraicCurve.SemilinearAut K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) X]
        (x : X) (d d' : (ZMod N)ˣ),
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N (d * d'))) • x =
          AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d)) •
            AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d')) • x) ∧
    (∀ (X : Type u) [MulAction (AlgebraicCurve.SemilinearAut K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) X]
        (x : X) (d : (ZMod N)ˣ), d ∈ H' →
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d)) • x = x) ∧
    (∀ (X : Type u) [MulAction (AlgebraicCurve.SemilinearAut K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) X]
        (x : X) (d : (ZMod N)ˣ),
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d)) •
            AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹)) • x = x ∧
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹)) •
            AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d)) • x = x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul.solution
