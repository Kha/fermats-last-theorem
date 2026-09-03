import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_FVectStructure
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_fVectStructure_normalForm_model_of_finite_flat_of_inertiaSimple_step
attribute [-instance] AlgebraicClosure.Rat.isGalois CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul

theorem HopfAlgebra.exists_fVectStructure_normalForm_model_of_finite_flat_of_inertiaSimple_step
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
    (hKK' : K ≤ K')
    (hK : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K))
    (hK' : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K'))
    (hstep : ∀ S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      K ≤ S → S ≤ K' →
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ S,
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ S) →
      S = K ∨ S = K')
    (s : ℕ) [NeZero s] (hcard : Nat.card K' = p ^ s * Nat.card K) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R' ↥P)
        (F : Type) (_ : Field F) (_ : Fintype F)
        (B : Type) (_ : CommRing B) (_ : HopfAlgebra R' B)
        (fv : HopfAlgebra.FVectStructure F R' B)
        (χ : Fˣ →* R'ˣ) (ι₀ : F →+* IsLocalRing.ResidueField ↥P)
        (X : Fin s → B) (δ : Fin s → R')
        (q : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → (B →ₐ[R'] ↥P)),
        Irreducible (p : R') ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ r : R',
          σ ((algebraMap R' ↥P r : ↥P) : AlgebraicClosure ℚ) = (algebraMap R' ↥P r : ↥P)) ∧
        Fintype.card F = p ^ s ∧
        (∀ l : Fˣ, IsLocalRing.residue ↥P (algebraMap R' ↥P ((χ l : R'ˣ) : R')) = ι₀ l) ∧
        (∀ (i : Fin s) (l : Fˣ), fv.act l (X i) = (((χ ^ (p ^ (i : ℕ))) l : R'ˣ) : R') • X i) ∧
        (∀ i, X i ^ p = δ i • X (i + 1)) ∧
        (∀ i, δ i ∣ (p : R')) ∧
        (∀ i, Coalgebra.counit (R := R') (X i) = 0) ∧
        Algebra.adjoin R' (Set.range X) = ⊤ ∧
        Nat.card (B →ₐ[R'] ↥P) = p ^ s ∧
        (∀ f ∈ K', ∀ g ∈ K',
          WithConv.toConv (q (f * g)) = WithConv.toConv (q f) * WithConv.toConv (q g)) ∧
        (∀ f ∈ K', (WithConv.toConv (q f) = 1 ↔ f ∈ K)) ∧
        (∀ b : B →ₐ[R'] ↥P, ∃ f ∈ K', q f = b) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
          ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → ∀ x : B,
              ((q g x : ↥P) : AlgebraicClosure ℚ) = σ ((q f x : ↥P) : AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_fVectStructure_normalForm_model_of_finite_flat_of_inertiaSimple_step.solution
