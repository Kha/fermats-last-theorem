import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_FVectStructure
import Definitions.Def_HopfAlgebra_HasFVectDevissage
import P2M.Util
import P2M.Sol.S_HopfAlgebra_hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField
attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions
attribute [-simp] HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField
    (R : Type u) [CommRing R] [IsLocalRing R] (K : Type u) [Field K] [PerfectField K] [Algebra R K]
    (p : ℕ) [Fact p.Prime] (N n : ℕ)
    (hT : ∀ s : ℕ, 0 < s → s ≤ N → ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = p ^ s →
      IsUnit ((p ^ s : R) - 1) ∧
        ∃ (χ : Fˣ →* Rˣ) (ι : F →+* IsLocalRing.ResidueField R),
          ∀ l : Fˣ, IsLocalRing.residue R (χ l : R) = ι l)
    (A : Type v) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Finite (WithConv (A →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (A →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : A →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] A →ₐ[AlgebraicClosure K]
          (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)))
    (hcard : Nat.card (WithConv (A →ₐ[K] AlgebraicClosure K)) ≤ p ^ N)
    (htors : ∀ ν : WithConv (A →ₐ[K] AlgebraicClosure K), ν ^ p ^ n = 1)
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [IsGalois K L]
    (hL : ∀ (ν : A →ₐ[K] AlgebraicClosure K) (a : A), ν a ∈ L)
    (hΓ : ∃ P : Subgroup (L ≃ₐ[K] L), P.Normal ∧ IsPGroup p ↥P ∧
      ∀ a b : (L ≃ₐ[K] L), a⁻¹ * b⁻¹ * a * b ∈ P) :
    HopfAlgebra.HasFVectDevissage R K p A := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField.solution
