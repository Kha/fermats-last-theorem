import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_isFinite_and_flat_and_surjective_of_isPullback_frobenius
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] AlgebraicGeometry.Scheme.relFrobenius_snd AlgebraicGeometry.Scheme.frobenius_preimage AlgebraicGeometry.Scheme.relFrobenius_fst AlgebraicGeometry.Scheme.relFrobenius_snd_assoc AlgebraicGeometry.Scheme.relFrobenius_fst_assoc AlgebraicGeometry.powCharRingHom_apply AlgebraicGeometry.Scheme.frobenius_base RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.isFinite_and_flat_and_surjective_of_isPullback_frobenius
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (pr : X' ⟶ X)
    (hpr : IsPullback pr f' f (Spec.map (CommRingCat.ofHom (frobenius k p))))
    (F : X ⟶ X') (hF : F ≫ f' = f)
    (hFrob : ∀ (B : Type u) [CommRing B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
      x ≫ F ≫ pr = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x) :
    IsFinite F ∧ Flat F ∧ LocallyOfFinitePresentation F ∧ Surjective F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_isFinite_and_flat_and_surjective_of_isPullback_frobenius.solution
