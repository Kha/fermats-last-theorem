import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation

set_option autoImplicit false

open CategoryTheory

universe u

theorem RingHom.isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A]
    (s t : A →+* B)
    (hs : letI := s.toAlgebra; Module.Finite A B) (hs' : letI := s.toAlgebra; Module.Projective A B)
    (ht : letI := t.toAlgebra; Module.Finite A B) (ht' : letI := t.toAlgebra; Module.Projective A B)
    (hgen : s.range ⊔ t.range = ⊤)
    (hequiv : ∀ (T : Type u) [CommRing T],
      _root_.Equivalence fun x y : A →+* T => ∃ φ : B →+* T, φ.comp s = x ∧ φ.comp t = y)
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀ a : A, s a = t a ↔ a ∈ Set.range (algebraMap C A)) :
    Module.Finite C A ∧ Module.Projective C A ∧ Module.FaithfullyFlat C A ∧
      IsPushout (CommRingCat.ofHom (algebraMap C A)) (CommRingCat.ofHom (algebraMap C A))
        (CommRingCat.ofHom s) (CommRingCat.ofHom t) := by p2m_exact_reverting @_root_.P2MW.S_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation.solution
