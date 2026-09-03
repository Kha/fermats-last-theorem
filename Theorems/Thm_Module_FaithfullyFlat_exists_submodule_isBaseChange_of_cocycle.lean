import Mathlib
import Definitions.Def_Algebra_DescentCofaces
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_exists_submodule_isBaseChange_of_cocycle

universe u

open TensorProduct CategoryTheory Algebra.DescentCofaces
theorem Module.FaithfullyFlat.exists_submodule_isBaseChange_of_cocycle
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (N : Type u) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (φ' : (ModuleCat.extendScalars (i₁ A B).hom).obj (ModuleCat.of B N) ≅
      (ModuleCat.extendScalars (i₂ A B).hom).obj (ModuleCat.of B N))
    (hcocycle : Cocycle (ModuleCat.of B N) φ'.hom) :
    ∃ M : Submodule A N,
      (∀ n : N, n ∈ M ↔
        φ'.hom (((1 : B ⊗[A] B) ⊗ₜ[B] n : (ModuleCat.extendScalars (i₁ A B).hom).obj (ModuleCat.of B N))) =
          ((1 : B ⊗[A] B) ⊗ₜ[B] n : (ModuleCat.extendScalars (i₂ A B).hom).obj (ModuleCat.of B N))) ∧
      IsBaseChange B M.subtype ∧
      (∃ θ : (ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A M) ≅ ModuleCat.of B N,
        (∀ (b : B) (m : M),
          θ.hom ((b ⊗ₜ[A] m : (ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A M))) = b • (m : N)) ∧
        (ModuleCat.extendScalars (i₁ A B).hom).map θ.hom ≫ φ'.hom =
          canonical A B (ModuleCat.of A M) ≫ (ModuleCat.extendScalars (i₂ A B).hom).map θ.hom) ∧
      (Module.Invertible B N → Module.Invertible A M) := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_exists_submodule_isBaseChange_of_cocycle.solution
