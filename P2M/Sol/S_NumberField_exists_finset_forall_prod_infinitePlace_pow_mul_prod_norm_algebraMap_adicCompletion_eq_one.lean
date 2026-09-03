import Mathlib
import P2M.Util
namespace P2MW.S_NumberField_exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain

open NumberField in

theorem solution
    (K : Type) [Field K] [NumberField K] (x : K) (hx : x ≠ 0) :
    ∃ T₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ T : Finset (HeightOneSpectrum (𝓞 K)), T₀ ⊆ T →
      (∏ v : InfinitePlace K, v x ^ v.mult) *
          ∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) x‖ = 1 := by
  classical
  have hfin : (Function.mulSupport fun w : FinitePlace K => w x).Finite :=
    FinitePlace.hasFiniteMulSupport hx
  refine ⟨hfin.toFinset.image FinitePlace.maximalIdeal, fun T hT => ?_⟩
  have key : ∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) x‖ = ∏ᶠ w : FinitePlace K, w x := by
    rw [finprod_eq_prod_of_mulSupport_subset (fun w : FinitePlace K => w x)
      (s := T.image FinitePlace.mk) ?_]
    · rw [Finset.prod_image (fun a _ b _ h => FinitePlace.mk_eq_iff.mp h)]
      rfl
    · intro w hw
      rw [Finset.coe_image]
      exact ⟨w.maximalIdeal, hT (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hw)),
        FinitePlace.mk_maximalIdeal w⟩
  rw [key]
  exact NumberField.prod_abs_eq_one hx
