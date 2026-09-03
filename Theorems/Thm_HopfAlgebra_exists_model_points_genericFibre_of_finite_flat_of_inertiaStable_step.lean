import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step
attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul

open scoped TensorProduct
theorem HopfAlgebra.exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step
    {p : ℕ} (hp : p.Prime)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
    (hKK' : K ≤ K')
    (hK : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K))
    (hK' : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K'))
    (s : ℕ) (hcard : Nat.card K' = p ^ s * Nat.card K)
    [Algebra ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ↥P]
    (hiP : ∀ x : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))),
      ((algebraMap ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ↥P x : ↥P) : AlgebraicClosure ℚ) = ((x : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ))
    (hDVR : IsDiscreteValuationRing ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hirr : Irreducible ((p : ℕ) : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))) :
    ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B)
        (_ : Module.Finite ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B) (_ : Module.Free ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B) (_ : Coalgebra.IsCocomm ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B),
      Module.finrank ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B = p ^ s ∧
      (∀ (T : Type) [CommRing T] [Algebra ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) T] (f : WithConv (B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] T)), f ^ p ^ 1 = 1) ∧
      ∃ (A₁ : Type) (_ : CommRing A₁) (_ : HopfAlgebra ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) A₁) (_ : Module.Finite ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) A₁)
          (_ : Coalgebra.IsCocomm ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) A₁) (_ : Finite (WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ)))
          (e : A₁ ≃ₐc[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) ⊗[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] B)
          (r : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ))
          (q : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → (B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] ↥P)),
        Function.Bijective
          (Algebra.TensorProduct.lift
            (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
            (Pi.algHom ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) _
              fun ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) =>
                (WithConv.ofConv ν : A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ))
            (fun _ _ => Commute.all _ _) :
            AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] A₁ →ₐ[AlgebraicClosure ℚ]
              (WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)) ∧
        (∀ f ∈ K', ∀ g ∈ K', r (f * g) = r f * r g) ∧
        (∀ f ∈ K', ∀ g ∈ K', (r f = r g ↔ ∃ k ∈ K, g = f * k)) ∧
        (∀ f ∈ K', (r f = 1 ↔ f ∈ K)) ∧
        (∀ ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ), ∃ f ∈ K', r f = ν) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
          ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → ∀ a : A₁, r g a = σ (r f a)) ∧
        Nat.card (B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] ↥P) = p ^ s ∧
        (∀ f ∈ K', ∀ g ∈ K',
          WithConv.toConv (q (f * g)) = WithConv.toConv (q f) * WithConv.toConv (q g)) ∧
        (∀ f ∈ K', (WithConv.toConv (q f) = 1 ↔ f ∈ K)) ∧
        (∀ b : B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] ↥P, ∃ f ∈ K', q f = b) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
          ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → ∀ x : B,
              ((q g x : ↥P) : AlgebraicClosure ℚ) = σ ((q f x : ↥P) : AlgebraicClosure ℚ)) ∧
        (∀ f ∈ K', ∀ b : B,
          ((q f b : ↥P) : AlgebraicClosure ℚ) = r f (e.symm ((1 : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) ⊗ₜ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] b))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step.solution
