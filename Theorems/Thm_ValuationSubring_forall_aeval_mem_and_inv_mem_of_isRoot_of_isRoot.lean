import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot

set_option autoImplicit false

theorem ValuationSubring.forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot
    (A : Type*) [CommRing A] [IsLocalRing A] (K' : Type*) [Field K'] [Algebra A K']
    (V : ValuationSubring K')
    (hA : ∀ a : A, algebraMap A K' a ∈ V) (hAm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A K' a ∈ V.nonunits)
    (J J' : K')
    (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic)
    (hΦJ : (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K') J)).IsRoot J')
    (Ψ : Polynomial (Polynomial ℤ)) (hΨ : Ψ.Monic)
    (hΨJ : (Ψ.map (Polynomial.eval₂RingHom (Int.castRingHom K') J')).IsRoot J)
    (hgen : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval J P ∈ V ∧ (Polynomial.aeval J P)⁻¹ ∈ V) :
    ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval J' P ∈ V ∧ (Polynomial.aeval J' P)⁻¹ ∈ V := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot.solution
