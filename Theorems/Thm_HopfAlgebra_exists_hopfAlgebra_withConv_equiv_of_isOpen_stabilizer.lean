import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer

set_option autoImplicit false

theorem HopfAlgebra.exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer
    (F L : Type) [Field F] [Field L] [Algebra F L] [IsGalois F L]
    (N : Type) [AddCommGroup N] [Finite N] [DistribMulAction (L ≃ₐ[F] L) N]
    (hN : ∀ x : N, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L))) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra F A),
      Module.Finite F A ∧ Coalgebra.IsCocomm F A ∧
      ∃ e : WithConv (A →ₐ[F] L) ≃ N,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : L ≃ₐ[F] L) (f g : WithConv (A →ₐ[F] L)),
          (∀ a : A, g a = σ (f a)) → e g = σ • e f := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer.solution
