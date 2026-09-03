import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
namespace P2MW.S_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers

set_option autoImplicit false

theorem solution (K : Type) [Field K]
    [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : v.adicCompletion K) (hx : x ∈ v.adicCompletionIntegers K) :
    NumberField.StandardAddChar.psiLocal K v x = 1 := by
  have key : ∀ (y : v.adicCompletion K), Valued.v y ≤ 1 →
      NumberField.StandardAddChar.psiLocal K v y = 1 := by
    intro y hy
    rw [NumberField.StandardAddChar.psiLocal_apply,
      show NumberField.StandardAddChar.stdAddChar K
        = (NumberField.StandardAddChar.adelicTraceData K).psiK from rfl,
      NumberField.StandardAddChar.AdelicTraceData.psiK_apply,
      NumberField.StandardAddChar.AdelicTraceData.adelicTrace_apply,
      NumberField.StandardAddChar.psiQ_apply]
    change NumberField.StandardAddChar.psiArch
        ((NumberField.StandardAddChar.adelicTraceData K).traceInf 0)
      * NumberField.StandardAddChar.psiFin (NumberField.StandardAddChar.traceFinHom K
          (NumberField.StandardAddChar.finAdeleSingleAt K v y)) = 1
    have hint : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NumberField.StandardAddChar.finAdeleSingleAt K v y w ∈ w.adicCompletionIntegers K := by
      intro w
      by_cases hw : w = v
      · subst hw
        rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_self]
        exact hy
      · rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne K v y hw]
        exact zero_mem _
    let z : Π w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        w.adicCompletionIntegers K := fun w => ⟨_, hint w⟩
    have hsm : RestrictedProduct.structureMap
          (fun w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
            w.adicCompletion K)
          (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite z
        = NumberField.StandardAddChar.finAdeleSingleAt K v y :=
      RestrictedProduct.ext _ _ fun w => rfl
    rw [← hsm, NumberField.StandardAddChar.traceFinHom_structureMap, map_zero,
      AddChar.map_zero_eq_one, one_mul]
    exact NumberField.StandardAddChar.psiFin_eq_one_of_forall_mem _ fun w =>
      (NumberField.AdelicTrace.traceInt K z w).2
  exact key x hx
