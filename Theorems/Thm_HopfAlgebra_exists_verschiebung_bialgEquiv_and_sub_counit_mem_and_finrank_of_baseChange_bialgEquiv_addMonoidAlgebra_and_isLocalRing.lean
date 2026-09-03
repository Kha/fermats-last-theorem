import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra R (ZMod p)]
    (hres : ∀ x : R, algebraMap R (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R)
    (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)] [Module.Flat R A]
    [FaithfulSMul R A] [CharP (IsLocalRing.ResidueField A) p]
    (C : Type) [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C] [Module.Free R C] [Module.Finite R C]
    (Λ : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (n : ℕ) (hΛ : Fintype.card Λ = p ^ n)
    (e : A ⊗[R] C ≃ₐc[A] AddMonoidAlgebra A Λ) :
    (∃ Ver : ZMod p ⊗[R] C ≃ₐc[ZMod p] ZMod p ⊗[R] C,
      ∀ χ : CartierDual (ZMod p) (ZMod p ⊗[R] C), CartierDual.map (Ver : ZMod p ⊗[R] C →ₐc[ZMod p] ZMod p ⊗[R] C) χ = χ ^ p) ∧
    (∀ (χ : C →ₐ[R] A) (c : C), χ c - algebraMap R A (Coalgebra.counit c) ∈ IsLocalRing.maximalIdeal A) ∧
    Module.finrank R C = Fintype.card Λ ∧

    IsLocalRing (IsLocalRing.ResidueField A ⊗[R] C) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing.solution
