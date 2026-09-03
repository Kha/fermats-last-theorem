import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_exists_towerHom_map_comp_eq_comp_of_map_L_le
attribute [-instance] MvFormalGroup.instIsCommAddMv MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode
attribute [-simp] HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

universe u

theorem Deformation.HondaSystem.exists_towerHom_map_comp_eq_comp_of_map_L_le
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (L : ℕ → Type u) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * r))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v))
    (hunipL : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v))))
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)))
    (hπs : ∀ v, Function.Surjective (π v))
    (hπk : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) =
      Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)) (π v x))
    (hπV : ∀ v x, π v (H₁.V x) =
      Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)) (π v x))
    (hπL : ∀ v, (Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight :
          L v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L v)).toRingHom).toAddSubgroup =
      H₁.L.toAddSubgroup.map (π v))
    (hπt : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v)) (π (v + 1) x) = π v x)
    (r' : ℕ) (H₂ : Deformation.HondaSystem (p : 𝓞) (Fin r' → 𝓞))
    (L' : ℕ → Type u) [∀ v, CommRing (L' v)] [∀ v, HopfAlgebra 𝓞 (L' v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L' v)] [∀ v, Module.Free 𝓞 (L' v)] [∀ v, Module.Finite 𝓞 (L' v)]
    (t' : ∀ v, L' (v + 1) →ₐc[𝓞] L' v) (ht' : ∀ v, Function.Surjective (t' v))
    (hrankL' : ∀ v, Module.finrank 𝓞 (L' v) = p ^ (v * r'))
    (hkerL' : ∀ v, RingHom.ker (t' v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L' (v + 1)) (p ^ v))
    (hunipL' : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L' v))))
    (π' : ∀ v, (Fin r' → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L' v)))
    (hπ's : ∀ v, Function.Surjective (π' v))
    (hπ'k : ∀ v x, π' v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπ'F : ∀ v x, π' v (H₂.F x) =
      Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L' v)) (π' v x))
    (hπ'V : ∀ v x, π' v (H₂.V x) =
      Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L' v)) (π' v x))
    (hπ'L : ∀ v, (Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight :
          L' v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L' v)).toRingHom).toAddSubgroup =
      H₂.L.toAddSubgroup.map (π' v))
    (hπ't : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t' v)) (π' (v + 1) x) = π' v x)
    (φ : (Fin r' → 𝓞) →ₗ[𝓞] (Fin r → 𝓞))
    (hφF : φ ∘ₗ H₂.F = H₁.F ∘ₗ φ) (hφV : φ ∘ₗ H₂.V = H₁.V ∘ₗ φ)
    (hφL : Submodule.map φ H₂.L ≤ H₁.L) :
    ∃ f : ∀ v, L' v →ₐc[𝓞] L v,
      (∀ v, (f v).comp (t' v) = (t v).comp (f (v + 1))) ∧
      ∀ v x, Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (f v)) (π' v x) = π v (φ x) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_exists_towerHom_map_comp_eq_comp_of_map_L_le.solution
