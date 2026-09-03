import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent

set_option autoImplicit false

universe u

theorem MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent
    {R : Type u} [CommRing R] (d : ℕ)
    (μ : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (Fin d → C) → (Fin d → C) → (Fin d → C))
    (hμ_mem : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) → ∀ j, μ C J x y j ∈ J)
    (hμ_zero : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin d → C, (∀ j, x j ∈ J) → μ C J x 0 = x ∧ μ C J 0 x = x)
    (hμ_assoc : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
      ∀ x y z : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) → (∀ j, z j ∈ J) →
        μ C J (μ C J x y) z = μ C J x (μ C J y z))
    (hμ_comm : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) → μ C J x y = μ C J y x)
    (hμ_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
          μ C' J' (φ ∘ x) (φ ∘ y) = φ ∘ μ C J x y) :
    ∃! Φ : MvFormalGroup d R, Φ.IsComm ∧
      ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
        ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
          ∀ i, μ C J x y i = MvFormalGroup.adicEval J (Sum.elim x y) (Φ.toPowerSeries i) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent.solution
