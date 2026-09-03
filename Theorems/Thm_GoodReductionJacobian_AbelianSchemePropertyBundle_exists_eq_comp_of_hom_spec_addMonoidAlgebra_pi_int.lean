import Mathlib
import Definitions.Def_JacJ1Iface
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
    {k : Type u} [Field k] [IsAlgClosed k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    (hA : AbelianSchemePropertyBundle k f) (t : ℕ)
    (φ : Spec (CommRingCat.of (AddMonoidAlgebra k (Fin t → ℤ))) ⟶ A)
    (hφ : φ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Fin t → ℤ))))) :
    ∃ a : Spec (CommRingCat.of k) ⟶ A, a ≫ f = 𝟙 _ ∧
      φ = Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Fin t → ℤ)))) ≫ a := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int.solution
