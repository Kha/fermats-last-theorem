import Mathlib
import P2M.Util
import P2M.Sol.S_CommRingCat_isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

theorem CommRingCat.isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective
    {P C' C'' C₀ A A' A'' A₀ : CommRingCat.{u}}
    {p' : P ⟶ C'} {p'' : P ⟶ C''} {φ' : C' ⟶ C₀} {φ'' : C'' ⟶ C₀} (hC : IsPullback p' p'' φ' φ'')
    {a' : A ⟶ A'} {a'' : A ⟶ A''} {q' : A' ⟶ A₀} {q'' : A'' ⟶ A₀} (hA : IsPullback a' a'' q' q'')
    (u : P ⟶ A) (u' : C' ⟶ A') (u'' : C'' ⟶ A'') (u₀ : C₀ ⟶ A₀)
    (hu' : p' ≫ u' = u ≫ a') (hu'' : p'' ≫ u'' = u ≫ a'') (hq' : φ' ≫ u₀ = u' ≫ q') (hq'' : φ'' ≫ u₀ = u'' ≫ q'')
    (hφ' : Function.Surjective φ'.hom) (hφ'' : Function.Surjective φ''.hom)
    (hco' : IsPushout φ' u' u₀ q') (hco'' : IsPushout φ'' u'' u₀ q'') :
    IsPushout p' u u' a' ∧ IsPushout p'' u u'' a'' := by p2m_exact_reverting @_root_.P2MW.S_CommRingCat_isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective.solution
