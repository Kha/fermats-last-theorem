import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemilinearAut_existsUnique_monoidHom_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension

open AlgebraicCurve

theorem AlgebraicCurve.SemilinearAut.existsUnique_monoidHom_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (S : Type*) [Group S] (galF : S →* SemilinearAut K F) (τ : S →* (K' ≃+* K'))
    (hτ : ∀ (σ : S) (a : K), τ σ (algebraMap K K' a) = algebraMap K K' (SemilinearAut.baseAut (galF σ) a)) :
    ∃! galF' : S →* SemilinearAut K' F',
      (∀ (σ : S) (c : K'), SemilinearAut.baseAut (galF' σ) c = τ σ c) ∧
      ∀ (σ : S) (y : F), galF' σ • algebraMap F F' y = algebraMap F F' (galF σ • y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_existsUnique_monoidHom_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension.solution
