import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import P2M.Util
namespace P2MW.S_AutomorphicForm_rightConv_mul_ideleNorm_det_rpow_neg_half

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] (w : ℝ)
    (φ f f' : AdelicGL2 (𝓞 K) K → ℂ)
    (hff' : ∀ g : AdelicGL2 (𝓞 K) K,
      f' g = f g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ))
    (g : AdelicGL2 (𝓞 K) K) :
    rightConv K (fun g : AdelicGL2 (𝓞 K) K => φ g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ)) f' g =
      rightConv K φ f g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ) := by
  rw [rightConv_apply, rightConv_apply]
  rw [← integral_mul_const]
  congr 1
  funext x
  have hgx : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) :=
    NumberField.TateGlobal.ideleNorm_pos _
  have hg : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) :=
    NumberField.TateGlobal.ideleNorm_pos _
  have h1 : (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x)) ^ (-(w / 2)) : ℝ) : ℂ) *
      (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x)) ^ (w / 2) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hgx, show -(w / 2) + w / 2 = (0 : ℝ) by ring, Real.rpow_zero,
      Complex.ofReal_one]
  have hsplit : (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (g * x))) ^ (-(w / 2)) : ℝ) : ℂ) =
      (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ) *
      (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x)) ^ (-(w / 2)) : ℝ) : ℂ) := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, Real.mul_rpow hg.le hgx.le, Complex.ofReal_mul]
  rw [hff' x, hsplit]
  linear_combination (φ (g * x) * f x *
    (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ)) * h1
