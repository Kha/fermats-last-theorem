import Mathlib
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_restrictAlong_congrEquiv_and_existsUnique_iff

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K E F F' : Type*} [Field K] [Field E] [Field F] [Field F'] [Algebra K E] [Algebra K F] [Algebra K F']
    (φ : E →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (φ' : E →ₐ[K] F') (hφ' : φ'.toRingHom.IsIntegral)
    (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
    (hcomm : ∀ x : E, e (φ x) = φ' x) :
    (∀ w : Place K F, (Place.congrEquiv e he w).restrictAlong φ' hφ' = w.restrictAlong φ hφ) ∧
    (∀ s : Place K E, ∀ w' : Place K F', w'.restrictAlong φ' hφ' = s ↔
        ((Place.congrEquiv e he).symm w').restrictAlong φ hφ = s) ∧
    (∀ s : Place K E, (∃! w : Place K F, w.restrictAlong φ hφ = s) ↔
        (∃! w' : Place K F', w'.restrictAlong φ' hφ' = s)) := by
  classical
  have h1 : ∀ w : Place K F, (Place.congrEquiv e he w).restrictAlong φ' hφ' = w.restrictAlong φ hφ := by
    intro w
    apply Place.ext
    ext x
    show (e.symm : F' →+* F) (φ'.toRingHom x) ∈ w.toValuationSubring ↔ φ.toRingHom x ∈ w.toValuationSubring
    rw [show φ'.toRingHom x = φ' x from rfl, show φ.toRingHom x = φ x from rfl, ← hcomm]
    show e.symm (e (φ x)) ∈ w.toValuationSubring ↔ φ x ∈ w.toValuationSubring
    rw [e.symm_apply_apply]
  have h2 : ∀ s : Place K E, ∀ w' : Place K F', w'.restrictAlong φ' hφ' = s ↔
      ((Place.congrEquiv e he).symm w').restrictAlong φ hφ = s := by
    intro s w'
    rw [← h1 ((Place.congrEquiv e he).symm w'), Equiv.apply_symm_apply]
  refine ⟨h1, h2, fun s => ?_⟩
  constructor
  · rintro ⟨w, hw, huniq⟩
    refine ⟨Place.congrEquiv e he w, by show Place.restrictAlong φ' hφ' (Place.congrEquiv e he w) = s; rw [h1]; exact hw, fun w' hw' => ?_⟩
    have := huniq ((Place.congrEquiv e he).symm w') ((h2 s w').mp hw')
    rw [← this, Equiv.apply_symm_apply]
  · rintro ⟨w', hw', huniq⟩
    refine ⟨(Place.congrEquiv e he).symm w', (h2 s w').mp hw', fun w hw => ?_⟩
    have := huniq (Place.congrEquiv e he w) (by show Place.restrictAlong φ' hφ' (Place.congrEquiv e he w) = s; rw [h1]; exact hw)
    rw [← this, Equiv.symm_apply_apply]

#print axioms solution
