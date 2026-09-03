import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvPowerSeries_existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent

set_option autoImplicit false

universe u

theorem MvPowerSeries.existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent
    {R : Type u} [CommRing R] {σ : Type} [Finite σ]
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x)) :
    ∃! f : MvPowerSeries σ R,
      ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C J x = MvFormalGroup.adicEval J x f := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent.solution
