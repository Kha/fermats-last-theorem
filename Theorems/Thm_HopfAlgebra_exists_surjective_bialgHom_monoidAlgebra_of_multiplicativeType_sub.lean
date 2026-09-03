import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub
attribute [-instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra
attribute [-simp] GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply

theorem HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ))
    (hOA : (O : Set (AlgebraicClosure ℚ)) ⊆ A)
    (hOdvr : IsDiscreteValuationRing ↥O)
    (hOirr : Irreducible ((q : ℕ) : ↥O))
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x ∈ O, σ x = x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → y ∈ O)
    (H : Type) [CommRing H] [HopfAlgebra ↥O H]
    [Module.Finite ↥O H] [Module.Flat ↥O H] [Coalgebra.IsCocomm ↥O H]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M S : AddSubgroup J) (hSM : S ≤ M)
    (pts : WithConv (H →ₐ[↥O] AlgebraicClosure ℚ) ≃ ↥M)
    (hadd : ∀ f g, pts (f * g) = pts f + pts g)
    (hact : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f g : WithConv (H →ₐ[↥O] AlgebraicClosure ℚ),
      (∀ x : H, g x = σ (f x)) → ((pts g : ↥M) : J) = σ • ((pts f : ↥M) : J))
    (a : ℕ) (hcardS : Nat.card ↥S = q ^ a)
    (hS : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) → ∀ x ∈ S, σ • x = c • x) :
    ∃ p : H →ₐc[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q)),
      Function.Surjective p ∧
      ∀ f : H →ₐ[↥O] AlgebraicClosure ℚ,
        (∃ g : MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q)) →ₐ[↥O] AlgebraicClosure ℚ,
            g.comp (p : H →ₐ[↥O] MonoidAlgebra ↥O (Multiplicative (Fin a → ZMod q))) = f) ↔
          ((pts (WithConv.toConv f) : ↥M) : J) ∈ S := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub.solution
