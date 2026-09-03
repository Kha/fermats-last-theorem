import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Artin_exists_artinFieldCore_exists_artinPairCore_of_isAdmissibleModulusOfDegree
attribute [-instance] LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal
attribute [-simp] AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField LanglandsTunnell.P2.Artin

universe u v

theorem LanglandsTunnell.Artin.exists_artinFieldCore_exists_artinPairCore_of_isAdmissibleModulusOfDegree
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (ℓ k : ℕ) (hℓ : ℓ.Prime) (hexp : ∀ x : L ≃ₐ[K] L, x ^ (ℓ ^ k) = 1)
    (𝔣 : Ideal (𝓞 K)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree K L (ℓ ^ k) 𝔣)
    (σ : L ≃ₐ[K] L) :
    ∃ D : ∀ i : ↥(primeCarriers K 𝔣), ArtinFieldCore.{u, v, v, v, v} K L 𝔣 i,
      (∀ i : ↥(primeCarriers K 𝔣),
        NumberField.NormIndex.IsAdmissibleModulusOfDegree (D i).E (D i).N (ℓ ^ k)
          (HeckeCharacter.modulusExt K (D i).E (D i).𝔪)) ∧
      ∀ i j : ↥(primeCarriers K 𝔣),
        ∃ P : ArtinPairCore.{u, v, v, v, v, v, v, v, v, v} K L 𝔣 σ (D i) (D j),
          NumberField.NormIndex.IsAdmissibleModulusOfDegree P.E'' P.N'' (ℓ ^ k)
            (HeckeCharacter.modulusExt K P.E'' P.𝔪'') := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Artin_exists_artinFieldCore_exists_artinPairCore_of_isAdmissibleModulusOfDegree.solution
