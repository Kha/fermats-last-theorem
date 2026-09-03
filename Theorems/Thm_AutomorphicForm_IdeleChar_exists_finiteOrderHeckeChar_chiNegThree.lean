import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_ModularForm_EisensteinChiNegThree
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IdeleChar_exists_finiteOrderHeckeChar_chiNegThree
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.IdeleChar.exists_finiteOrderHeckeChar_chiNegThree :
    ∃ ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ,
      HeckeCharacter.IsFiniteOrderHeckeChar ℚ ω ∧
      HeckeCharacter.AdmitsModulus ℚ ω (Ideal.span {(3 : 𝓞 ℚ)}) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ≠ Ideal.span {(3 : 𝓞 ℚ)} →
        ((ω (AutomorphicForm.uniformizerIdele ℚ v) : ℂˣ) : ℂ)
          = ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℂ)) ∧
      (∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
        (u : AdeleRing (𝓞 ℚ) ℚ).1 = -1 → (u : AdeleRing (𝓞 ℚ) ℚ).2 = 1 →
        ((ω u : ℂˣ) : ℂ) = -1) ∧
      (∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
        (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 →
        (∀ w : HeightOneSpectrum (𝓞 ℚ), w.asIdeal ≠ Ideal.span {(3 : 𝓞 ℚ)} →
          ((u : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1) →
        (∀ w : HeightOneSpectrum (𝓞 ℚ), w.asIdeal = Ideal.span {(3 : 𝓞 ℚ)} →
          ((u : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) w = (3 : w.adicCompletion ℚ)) →
        ((ω u : ℂˣ) : ℂ) = 1) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IdeleChar_exists_finiteOrderHeckeChar_chiNegThree.solution
