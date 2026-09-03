import Mathlib
import P2M.Util
import P2M.Sol.S_CommRingCat_isPushout_tensorProduct_tensorProduct

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

theorem CommRingCat.isPushout_tensorProduct_tensorProduct
    (R : Type u) [CommRing R] (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] :
    IsPushout
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] C).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R A)
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] C)).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B ⊗[R] C →ₐ[R] A ⊗[R] (B ⊗[R] C)).toRingHom) := by p2m_exact_reverting @_root_.P2MW.S_CommRingCat_isPushout_tensorProduct_tensorProduct.solution
