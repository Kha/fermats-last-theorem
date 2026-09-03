import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isCocomm_of_isReduced_baseChange_of_withConv_equiv

open scoped TensorProduct
theorem HopfAlgebra.isCocomm_of_isReduced_baseChange_of_withConv_equiv
    (R : Type*) [CommRing R] (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (hinj : Function.Injective (algebraMap R Ω))
    (H : Type*) [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    [Module.Finite Ω (Ω ⊗[R] H)] [IsReduced (Ω ⊗[R] H)]
    {N : Type*} [AddCommGroup N] (e : WithConv (H →ₐ[R] Ω) ≃ N)
    (he : ∀ f g : WithConv (H →ₐ[R] Ω), e (f * g) = e f + e g) :
    Coalgebra.IsCocomm R H := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isCocomm_of_isReduced_baseChange_of_withConv_equiv.solution
