import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_ker_eq_torsionIdeal_of_baseChange_addMonoidAlgebra_of_surjective
attribute [-simp] PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.ker_eq_torsionIdeal_of_baseChange_addMonoidAlgebra_of_surjective
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsDomain R]
    (A : Type) [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]
    (C C' : Type) [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C] [Module.Free R C] [Module.Finite R C]
    [CommRing C'] [HopfAlgebra R C'] [Coalgebra.IsCocomm R C'] [Module.Free R C'] [Module.Finite R C']
    (Λ Λ' : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] [AddCommGroup Λ'] [Fintype Λ'] [DecidableEq Λ']
    (e : A ⊗[R] C ≃ₐc[A] AddMonoidAlgebra A Λ) (e' : A ⊗[R] C' ≃ₐc[A] AddMonoidAlgebra A Λ')
    (v : ℕ) (f : Λ' →+ Λ) (hf : Function.Surjective f) (hfker : ∀ x : Λ', f x = 0 ↔ ∃ y : Λ', x = (p ^ v) • y)
    (t : C' →ₐc[R] C) (ht : Function.Surjective t)
    (hte : ∀ z : A ⊗[R] C', e (Algebra.TensorProduct.map (AlgHom.id A A) (t : C' →ₐ[R] C) z) =
      AddMonoidAlgebra.mapDomainBialgHom A f (e' z)) :
    RingHom.ker t = PDivisibleGroup.Hopf.torsionIdeal R C' (p ^ v) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_ker_eq_torsionIdeal_of_baseChange_addMonoidAlgebra_of_surjective.solution
