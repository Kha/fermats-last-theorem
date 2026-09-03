import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_spanFinrank_ker_add_ringKrullDim_eq

open IsLocalRing

theorem IsRegularLocalRing.spanFinrank_ker_add_ringKrullDim_eq
    {A B : Type*} [CommRing A] [CommRing B] [IsRegularLocalRing A] [IsRegularLocalRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    ((RingHom.ker f).spanFinrank : WithBot ℕ∞) + ringKrullDim B = ringKrullDim A := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_spanFinrank_ker_add_ringKrullDim_eq.solution
