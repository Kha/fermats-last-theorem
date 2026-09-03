import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow
import P2M.Util
namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_isFactorizableTestFn_flat
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
open scoped ComplexConjugate

namespace FlatFactProof

variable {F : Type} [Field F] [NumberField F]

private theorem adelicArchGLIncl_glArch_mul_finEmbed_glFin (y : AdelicGL2 (𝓞 F) F) :
    adelicArchGLIncl F (glArch (𝓞 F) F y) * AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y) = y := by
  apply Units.ext
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · show ((glArch (𝓞 F) F (adelicArchGLIncl F (glArch (𝓞 F) F y) * AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y)) :
        GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
        = ((glArch (𝓞 F) F y : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix _ _ _)
    rw [map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one]
  · show ((glFin (𝓞 F) F (adelicArchGLIncl F (glArch (𝓞 F) F y) * AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
        = ((glFin (𝓞 F) F y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix _ _ _)
    rw [map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul]

end FlatFactProof

open FlatFactProof in
theorem solution
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    IsFactorizableTestFn F (flat F σ f) := by
  obtain ⟨fa, ff, hfa, hff, hfeq⟩ := hf
  refine ⟨fun y => conj (fa y⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F y)) ^ (-σ) : ℝ) : ℂ),
    fun b => conj (ff b⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F b)) ^ (-σ) : ℝ) : ℂ),
    AutomorphicForm.CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow F σ fa hfa,
    AutomorphicForm.CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow F σ ff hff, fun g => ?_⟩
  show conj (f g⁻¹) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-σ) : ℝ) : ℂ) = _

  have hdet : Matrix.GeneralLinearGroup.det g
      = Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (glArch (𝓞 F) F g))
        * Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F g)) := by
    rw [← map_mul, FlatFactProof.adelicArchGLIncl_glArch_mul_finEmbed_glFin]
  have hN : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-σ)
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (glArch (𝓞 F) F g))) ^ (-σ)
        * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F g))) ^ (-σ) := by
    rw [hdet, NumberField.TateGlobal.ideleNorm_mul,
      Real.mul_rpow (NumberField.TateGlobal.ideleNorm_pos _).le (NumberField.TateGlobal.ideleNorm_pos _).le]
  rw [hfeq, map_inv, map_inv, map_mul, hN, Complex.ofReal_mul]
  ring
