import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent
    {R C C' C₀ : CommRingCat.{u}} {fst : R ⟶ C} {snd : R ⟶ C'} {q : C ⟶ C₀} {q' : C' ⟶ C₀}
    (H : IsPullback fst snd q q') (hq' : Function.Surjective q'.hom)
    (hnil : ∀ x ∈ RingHom.ker q'.hom, IsNilpotent x) :
    IsPushout (Spec.map q) (Spec.map q') (Spec.map fst) (Spec.map snd) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent.solution
