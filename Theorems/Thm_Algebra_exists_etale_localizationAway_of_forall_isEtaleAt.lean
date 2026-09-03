import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_etale_localizationAway_of_forall_isEtaleAt

set_option autoImplicit false

open Polynomial TensorProduct

universe u

theorem Algebra.exists_etale_localizationAway_of_forall_isEtaleAt
    {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (hgen : ∀ (q : Ideal S) [q.IsPrime], q.comap (algebraMap R S) = ⊥ → Algebra.IsEtaleAt R q)
    (T : Finset (Ideal R)) (hT : ∀ p ∈ T, p.IsPrime)
    (hTet : ∀ p ∈ T, ∀ (q : Ideal S) [q.IsPrime], q.comap (algebraMap R S) = p → Algebra.IsEtaleAt R q) :
    ∃ c : R, c ≠ 0 ∧ (∀ p ∈ T, c ∉ p) ∧
      letI := (Localization.awayMap (algebraMap R S) c).toAlgebra
      Algebra.Etale (Localization.Away c) (Localization.Away (algebraMap R S c)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_etale_localizationAway_of_forall_isEtaleAt.solution
