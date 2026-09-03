import Mathlib
import Definitions.Def_Algebra_DescentCofaces
import P2M.Util
import P2M.Sol.S_Algebra_DescentCofaces_exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary

set_option autoImplicit false

open Algebra.DescentCofaces AlgebraicGeometry
open scoped TensorProduct
theorem Algebra.DescentCofaces.exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary
    (p : ℕ) (hp : p ≠ 0) (A : Type) [CommRing A] [Module.FaithfullyFlat ℤ A]
    (c : LocallyConstant (PrimeSpectrum (R₂ ℤ A)) (ZMod p))
    (hc : c.comap (Spec.topMap (c₁₂ ℤ A)).hom + c.comap (Spec.topMap (c₂₃ ℤ A)).hom =
        c.comap (Spec.topMap (c₁₃ ℤ A)).hom) :
    ∃ (B : Type) (_ : CommRing B) (_ : Nontrivial B) (_ : Module.Finite ℤ B) (_ : Module.Flat ℤ B)
      (_ : Algebra.FormallyUnramified ℤ B) (_ : A ⊗[ℤ] B ≃ₐ[A] (ZMod p → A)),
      Nonempty (B →+* ℤ) ↔
        ∃ b : LocallyConstant (PrimeSpectrum A) (ZMod p),
          c = b.comap (Spec.topMap (i₁ ℤ A)).hom - b.comap (Spec.topMap (i₂ ℤ A)).hom := by p2m_exact_reverting @_root_.P2MW.S_Algebra_DescentCofaces_exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary.solution
