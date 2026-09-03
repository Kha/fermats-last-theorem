import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_algHom_comp_hopfKer_val_eq_iff

universe u v w x
theorem HopfAlgebra.algHom_comp_hopfKer_val_eq_iff {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]
    {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : HopfAlgebra.IsHopfGalois π)
    {k : Type x} [CommRing k] [Algebra R k] (ψ ψ' : A →ₐ[R] k) :
    ψ.comp (HopfAlgebra.hopfKer π).val = ψ'.comp (HopfAlgebra.hopfKer π).val
      ↔ ∃! χ : B →ₐ[R] k,
          (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp (HopfAlgebra.coaction π) = ψ' := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_algHom_comp_hopfKer_val_eq_iff.solution
