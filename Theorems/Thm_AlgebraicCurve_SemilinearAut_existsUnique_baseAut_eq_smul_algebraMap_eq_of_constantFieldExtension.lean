import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemilinearAut_existsUnique_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension

p2m_open "AlgebraicCurve~linearIndependent_of_constantFieldExtension"

theorem AlgebraicCurve.SemilinearAut.existsUnique_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (g : SemilinearAut K F) (τ : K' ≃+* K')
    (hτ : ∀ a : K, τ (algebraMap K K' a) = algebraMap K K' (SemilinearAut.baseAut g a)) :
    ∃! g' : SemilinearAut K' F',
      (∀ c : K', SemilinearAut.baseAut g' c = τ c) ∧
      ∀ y : F, g' • algebraMap F F' y = algebraMap F F' (g • y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_existsUnique_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension.solution
