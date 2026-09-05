import Mathlib
import Theorems.Thm_ValuationSubring_toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian
import Theorems.Thm_HenselianLocalRing_of_isIntegral_of_isLocalRing
import P2M.Util
namespace P2MW.S_ValuationSubring_isDiscreteValuationRing_and_henselianLocalRing_comap_of_finiteDimensional

set_option autoImplicit false

open IsLocalRing

namespace HenselLayerAux

def incl {k K : Type} [Field k] [Field K] [Algebra k K] (O : ValuationSubring k) (O' : ValuationSubring K)
    (hO' : ∀ x : k, algebraMap k K x ∈ O' ↔ x ∈ O) : O →+* O' where
  toFun x := ⟨algebraMap k K x, (hO' x).mpr x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem core {k K : Type} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra.IsSeparable k K]
    (O : ValuationSubring k) [IsDiscreteValuationRing O] [HenselianLocalRing O]
    (O' : ValuationSubring K) (hO' : ∀ x : k, algebraMap k K x ∈ O' ↔ x ∈ O) :
    IsDiscreteValuationRing O' ∧ HenselianLocalRing O' := by
  classical
  haveI : IsScalarTower O k K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨h1, -, h3⟩ :=
    ValuationSubring.toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian O O' hO'
  have hdvr : IsDiscreteValuationRing O' := by
    have h3' : IsDiscreteValuationRing ↥(integralClosure ↥O K).toSubring := h3
    rw [← h1] at h3'
    exact h3'

  letI alg : Algebra O O' := (incl O O' hO').toAlgebra
  have halg : ∀ x : O, ((algebraMap O O' x : O') : K) = algebraMap k K x := fun x => rfl
  let g : O' →ₐ[O] K :=
    { toRingHom := O'.subtype
      commutes' := fun x => rfl }
  have hg : Function.Injective g := Subtype.val_injective
  haveI : Algebra.IsIntegral O O' := by
    refine ⟨fun y => ?_⟩
    have hy : (y : K) ∈ integralClosure (↥O) K := by
      have : (y : K) ∈ O'.toSubring := y.2
      rw [h1] at this
      exact this
    have hyK : IsIntegral O (y : K) := hy
    exact (isIntegral_algHom_iff g hg).mp hyK
  exact ⟨hdvr, HenselianLocalRing.of_isIntegral_of_isLocalRing (R := O) (S := O')⟩

end HenselLayerAux

theorem solution
    {F E : Type} [Field F] [Field E] [CharZero F] [Algebra F E] (halg : Algebra.IsAlgebraic F E)
    (A : ValuationSubring E) (k₀ : IntermediateField F E)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ E)))
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ E)))
    (K : IntermediateField ↥k₀ E) (hK : FiniteDimensional ↥k₀ ↥K) :
    IsDiscreteValuationRing ↥(A.comap (algebraMap ↥K E)) ∧ HenselianLocalRing ↥(A.comap (algebraMap ↥K E)) := by
  classical
  haveI := hK
  haveI := hdvr
  haveI := hhens
  haveI : CharZero ↥k₀ := charZero_of_injective_algebraMap (algebraMap F ↥k₀).injective
  haveI : Algebra.IsSeparable ↥k₀ ↥K := inferInstance
  have hO' : ∀ x : ↥k₀, algebraMap ↥k₀ ↥K x ∈ A.comap (algebraMap ↥K E) ↔ x ∈ A.comap (algebraMap ↥k₀ E) := by
    intro x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
    rfl
  exact HenselLayerAux.core (A.comap (algebraMap ↥k₀ E)) (A.comap (algebraMap ↥K E)) hO'

