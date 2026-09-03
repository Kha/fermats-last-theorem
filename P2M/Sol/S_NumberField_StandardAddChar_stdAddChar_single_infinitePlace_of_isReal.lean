import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicTraceFin
import P2M.Util
namespace P2MW.S_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isReal

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace PsiLine17

open scoped Classical in
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.StandardAddChar in

theorem infTraceSum_single_of_isReal (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (t : ℝ) : infTraceSum F (Pi.single w ((ringEquivRealOfIsReal hw).symm t)) = t := by
  unfold infTraceSum
  rw [Finset.sum_eq_single w]
  · rw [Pi.single_eq_same, mult_isReal ⟨w, hw⟩]
    have hre : (extensionEmbedding w ((ringEquivRealOfIsReal hw).symm t)).re = t := by
      rw [← extensionEmbeddingOfIsReal_apply hw, Complex.ofReal_re, ← ringEquivRealOfIsReal_apply,
        RingEquiv.apply_symm_apply]
    rw [hre]
    push_cast
    ring
  · intro w' _ hw'
    rw [Pi.single_eq_of_ne hw', map_zero, Complex.zero_re, mul_zero]
  · intro h; exact absurd (Finset.mem_univ w) h

open NumberField.StandardAddChar in

theorem psiArch_ratArchLine (t : ℝ) :
    psiArch (ratArchLine t) = Complex.exp (2 * Real.pi * Complex.I * t) := by
  have h1 : psiArch (ratArchLine t) = psiArchPlace default (ratArchLine t default) := by
    rw [psiArch_apply]
    exact finprod_unique _
  rw [h1, psiArchPlace_apply, ratArchLine_apply, ← NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    RingEquiv.apply_symm_apply]

end PsiLine17

open scoped Classical in
open PsiLine17 NumberField.StandardAddChar in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (t : ℝ) :
    NumberField.StandardAddChar.stdAddChar K
        (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t), 0)) =
      Complex.exp (2 * Real.pi * Complex.I * t) := by
  show (adelicTraceData K).psiK _ = _
  rw [AdelicTraceData.psiK_apply, AdelicTraceData.adelicTrace_apply, psiQ_apply]
  have hfin : (adelicTraceData K).traceFin
      ((show (AdeleRing (𝓞 K) K) from
        (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t), 0))).2 = 0 := by
    show (adelicTraceData K).traceFin 0 = 0
    exact map_zero _
  have hinf : (adelicTraceData K).traceInf
      ((show (AdeleRing (𝓞 K) K) from
        (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t), 0))).1 = ratArchLine t := by
    show traceInfHom K (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t)) = _
    rw [traceInfHom_apply, infTraceSum_single_of_isReal K w hw t]
  rw [hfin, AddChar.map_zero_eq_one, mul_one, hinf, psiArch_ratArchLine]
