import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_quotient_span_algebraMap_of_flat_of_isLocalHom_of_ringKrullDim_le_one

set_option autoImplicit false

universe u

open scoped TensorProduct

theorem IsRegularLocalRing.quotient_span_algebraMap_of_flat_of_isLocalHom_of_ringKrullDim_le_one
    {A : Type u} [CommRing A] (ϖ : A) (hmax : (Ideal.span {ϖ} : Ideal A).IsMaximal)
    (S : Type u) [CommRing S] [IsLocalRing S] [Algebra A S]
    (K' : Type u) [Field K'] [Algebra A K'] (hϖ : algebraMap A K' ϖ = 0)
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra (S ⊗[A] K') B] [Module.Flat (S ⊗[A] K') B]
    (hloc : IsLocalHom ((algebraMap (S ⊗[A] K') B).comp
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] K')))
    (hreg : IsRegularLocalRing B) (hdim : ringKrullDim B ≤ 1) :
    IsRegularLocalRing (S ⧸ Ideal.span {algebraMap A S ϖ}) := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_quotient_span_algebraMap_of_flat_of_isLocalHom_of_ringKrullDim_le_one.solution
