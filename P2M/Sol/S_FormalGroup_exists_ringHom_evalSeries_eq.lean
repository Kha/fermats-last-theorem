import Mathlib
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
namespace P2MW.S_FormalGroup_exists_ringHom_evalSeries_eq

set_option autoImplicit false

open FormalGroup

namespace EvalBridgeAux

theorem aux {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [uR : UniformSpace R] [DiscreteUniformity R]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T2Space A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (x : A) (hx : IsTopologicallyNilpotent x) :
    ∃ e : PowerSeries R →+* A,
      (∀ f : PowerSeries R, FormalGroup.evalSeries f x = e f) ∧
      (∀ p : Polynomial R, e (p : PowerSeries R) = Polynomial.eval₂ (algebraMap R A) x p) := by
  haveI : DiscreteTopology R := inferInstance
  have hφ : Continuous (algebraMap R A) := continuous_of_discreteTopology
  have ha : PowerSeries.HasEval x := (PowerSeries.hasEval_def x).mpr hx
  refine ⟨PowerSeries.eval₂Hom hφ ha, fun f => ?_, fun p => ?_⟩
  · rw [FormalGroup.evalSeries_eq_eval₂, PowerSeries.coe_eval₂Hom]
  · rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_coe]

end EvalBridgeAux

theorem solution
    {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (x : T) (hx : x ∈ I) :
    ∃ e : PowerSeries T →+* T,
      (∀ f : PowerSeries T, (letI : WithIdeal T := ⟨I⟩; FormalGroup.evalSeries f x) = e f) ∧
      (∀ p : Polynomial T, e (p : PowerSeries T) = p.eval x) := by
  letI wi : WithIdeal T := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hc, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I T)
  have hxn : IsTopologicallyNilpotent x := WithIdeal.isTopologicallyNilpotent_of_mem hx
  obtain ⟨e, he, hp⟩ := @EvalBridgeAux.aux T T _ _ (Algebra.id T) ⊥ inferInstance
    (WithIdeal.instUniformSpace T) inferInstance hc ht2 inferInstance inferInstance x hxn
  refine ⟨e, he, fun p => ?_⟩
  rw [hp p, Polynomial.eval₂_eq_eval_map]
  simp [Polynomial.map_id]
