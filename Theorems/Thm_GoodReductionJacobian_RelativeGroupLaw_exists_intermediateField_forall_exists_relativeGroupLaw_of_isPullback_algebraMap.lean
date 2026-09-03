import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_intermediateField_forall_exists_relativeGroupLaw_of_isPullback_algebraMap

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic~surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field NeronModelInfra GoodReductionJacobian"

theorem GoodReductionJacobian.RelativeGroupLaw.exists_intermediateField_forall_exists_relativeGroupLaw_of_isPullback_algebraMap
    (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (L : IntermediateField k K) [FiniteDimensional k ↥L]
    {A : Scheme.{0}} (fA : A ⟶ Spec (CommRingCat.of K)) (LA : RelativeGroupLaw K fA)
    {X₀ : Scheme.{0}} (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥L)) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFiniteType f₀]
    (g : A ⟶ X₀) (hg : CategoryTheory.IsPullback g fA f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥L K)))) :
    ∃ (Lm : IntermediateField k K) (_ : FiniteDimensional k ↥Lm) (_ : L ≤ Lm),
      ∀ (L'' : IntermediateField k K) (_ : Lm ≤ L'')
        (j : ↥L →+* ↥L'') (_ : ∀ x : ↥L, ((j x : ↥L'') : K) = (x : K))
        (X₂ : Scheme.{0}) (f₂ : X₂ ⟶ Spec (CommRingCat.of ↥L''))
        (r : A ⟶ X₂) (hr : CategoryTheory.IsPullback r fA f₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))))
        (q : X₂ ⟶ X₀) (_ : CategoryTheory.IsPullback q f₂ f₀ (Spec.map (CommRingCat.ofHom j))) (_ : r ≫ q = g),
        ∃ L₂ : RelativeGroupLaw ↥L'' f₂,
          (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' fA),
            (LA.mul t' P Q).1 ≫ r =
              (L₂.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K)))
                ⟨P.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, Q.2]⟩).1) ∧
          (LA.IsCommutative → L₂.IsCommutative) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_intermediateField_forall_exists_relativeGroupLaw_of_isPullback_algebraMap.solution
