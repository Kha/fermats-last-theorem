import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_bijective_withConv_algHomComp_of_finite_of_isAlgClosed

theorem HopfAlgebra.bijective_withConv_algHomComp_of_finite_of_isAlgClosed
    (K : Type) [Field K]
    (L₁ : Type) [Field L₁] [Algebra K L₁] [IsAlgClosed L₁]
    (L₂ : Type) [Field L₂] [Algebra K L₂] [IsAlgClosed L₂]
    (ι : L₁ →ₐ[K] L₂)
    (A : Type) [CommRing A] [HopfAlgebra K A] (hfin : Module.Finite K A) :
    Function.Bijective
      (fun f : WithConv (A →ₐ[K] L₁) => (WithConv.toConv (ι.comp f.ofConv) :
        WithConv (A →ₐ[K] L₂))) ∧
    ∀ f g : WithConv (A →ₐ[K] L₁),
      WithConv.toConv (ι.comp (f * g).ofConv)
        = WithConv.toConv (ι.comp f.ofConv) * WithConv.toConv (ι.comp g.ofConv) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_bijective_withConv_algHomComp_of_finite_of_isAlgClosed.solution
