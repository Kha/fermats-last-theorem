import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.Basic
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finite_free_quotient_bialgHom

universe u v w
theorem HopfAlgebra.exists_finite_free_quotient_bialgHom
    (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing A] [HopfAlgebra R A] [Module.Finite R A] :
    ∃ (B : Type v) (_ : CommRing B) (_ : HopfAlgebra R B) (π : A →ₐc[R] B),
      Module.Finite R B ∧ Module.Free R B ∧ Module.Flat R B ∧
      (Coalgebra.IsCocomm R A → Coalgebra.IsCocomm R B) ∧
      Function.Surjective ⇑π ∧
      ∀ (L : Type w) [CommRing L] [Algebra R L] [Module.IsTorsionFree R L],
        Function.Bijective (fun f : B →ₐ[R] L => f.comp (π : A →ₐ[R] B)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finite_free_quotient_bialgHom.solution
