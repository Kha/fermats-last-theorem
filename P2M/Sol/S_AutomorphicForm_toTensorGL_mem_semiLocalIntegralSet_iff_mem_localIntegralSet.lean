import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
namespace P2MW.S_AutomorphicForm_toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

namespace IntDescent

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem nonempty_extension : Nonempty (v.Extension (𝓞 L)) := by
  by_contra h
  rw [not_nonempty_iff] at h
  haveI : Subsingleton (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) := inferInstance
  have hinj := (HeightOneSpectrum.adicCompletion.baseChange_bijective K L (𝓞 L) v).1
  have h01 : ((1 : L) ⊗ₜ[K] (0 : v.adicCompletion K)) = (1 : L) ⊗ₜ[K] (1 : v.adicCompletion K) :=
    hinj (Subsingleton.elim _ _)
  have hι := Algebra.TensorProduct.includeRight_injective (R := K) (A := L) (B := v.adicCompletion K)
    (algebraMap K L).injective
  exact zero_ne_one (hι h01)

theorem one_tmul_mem_semiLocalIntegers_iff (x : v.adicCompletion K) :
    (1 : L) ⊗ₜ[K] x ∈ AutomorphicForm.semiLocalIntegers K L v ↔ x ∈ v.adicCompletionIntegers K := by
  constructor
  · intro hx
    rw [AutomorphicForm.semiLocalIntegers_eq_preimage] at hx
    obtain ⟨w⟩ := nonempty_extension K L v
    have hw := hx w (Set.mem_univ w)

    change (HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v ((1 : L) ⊗ₜ[K] x)) w ∈
      (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) at hw
    rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul] at hw
    change (w.adicCompletionSemialgHom K L x) ∈ w.1.adicCompletionIntegers L at hw
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      w.valued_adicCompletionSemialgHom K L] at hw
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact (pow_le_one_iff (IsDedekindDomain.HeightOneSpectrum.ramificationIdx_ne_zero (𝓞 K) (𝓞 L)
      (algebraMap_injective_of_field_isFractionRing (𝓞 K) (𝓞 L) K L) w.1)).1 hw
  · intro hx
    exact ⟨(1 : 𝓞 L) ⊗ₜ ⟨x, hx⟩, by
      rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, map_one]⟩

end IntDescent

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (s : GL (Fin 2) (v.adicCompletion K)) :
    AutomorphicForm.toTensorGL K L (v.adicCompletion K) s ∈ AutomorphicForm.semiLocalIntegralSet K L v ↔
      s ∈ AutomorphicForm.localIntegralSet K v := by
  have happ : ∀ (g : GL (Fin 2) (v.adicCompletion K)) (i j : Fin 2),
      ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j =
      (1 : L) ⊗ₜ[K] ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) := fun g i j => rfl
  rw [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.localIntegralSet,
    AutomorphicForm.mem_integralUnitsSet, AutomorphicForm.mem_integralUnitsSet, ← map_inv]
  simp only [happ, IntDescent.one_tmul_mem_semiLocalIntegers_iff, SetLike.mem_coe]

#print axioms solution
