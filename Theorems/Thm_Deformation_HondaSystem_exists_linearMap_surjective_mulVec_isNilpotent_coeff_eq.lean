import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq
attribute [-instance] Deformation.UnipotentWittCovector.instInhabited Deformation.UnipotentWittCovector.instAddCommGroup Deformation.TruncWitt.shiftLE_directedSystem Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra
attribute [-simp] Deformation.UnipotentWittCovector.lift_of Deformation.UnipotentWittCovector.of_shift Deformation.UnipotentWittCovector.frobenius_of Deformation.DieudonneModule.toCovector_of Deformation.TruncWitt.frobeniusAddHom_apply Deformation.UnipotentWittCovector.dieudonneDatum_F_apply Deformation.UnipotentWittCovector.map_of Deformation.UnipotentWittCovector.verschiebung_of Deformation.UnipotentWittCovector.dieudonneDatum_V_apply Deformation.DieudonneModule.evalMonoidHom_apply Deformation.DieudonneModule.eval_of Deformation.UnipotentWittCovector.of_shiftLE Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul
attribute [-simp] HopfAlgebra.canMap_tmul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem Deformation.HondaSystem.exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * r))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hunipG : ∀ v, IsLocalRing (CartierDual (ZMod p) (G v)))
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπ : ∀ v, Function.Surjective (π v))
    (hπker : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x))
    (hπV : ∀ v x, π v (H₁.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p (G v) (π v x))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
    (Gc₁ Ge₁ : Type v) [CommRing Gc₁] [HopfAlgebra (ZMod p) Gc₁] [Coalgebra.IsCocomm (ZMod p) Gc₁]
    [Module.Finite (ZMod p) Gc₁] [CommRing Ge₁] [HopfAlgebra (ZMod p) Ge₁] [Coalgebra.IsCocomm (ZMod p) Ge₁]
    [Module.Finite (ZMod p) Ge₁]
    (qc₁ : G 1 →ₐc[ZMod p] Gc₁) (πe₁ : G 1 →ₐc[ZMod p] Ge₁) (Θ₁ : G 1 →ₐc[ZMod p] Gc₁ ⊗[ZMod p] Ge₁)
    (hGc₁ : IsLocalRing Gc₁) (hGe₁ : IsReduced Ge₁) (hqc₁ : Function.Surjective qc₁)
    (hΘ₁ : Function.Bijective Θ₁)
    (hΘ₁apply : ∀ b, Θ₁ b = Algebra.TensorProduct.map (qc₁ : G 1 →ₐ[ZMod p] Gc₁) (πe₁ : G 1 →ₐ[ZMod p] Ge₁)
      (Coalgebra.comul (R := ZMod p) b))
    {d : ℕ} (κ₁ : MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] Gc₁) (hκ₁ : Function.Surjective κ₁)
    (hκ₁ε : ∀ i, Coalgebra.counit (R := ZMod p) (κ₁ (X i)) = 0)
    (hκ₁ker : RingHom.ker κ₁ ≤ (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ 2)
    (hd : d = Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) Gc₁).Cotangent) :
    ∃ (lam₀ lam₁ : H₁.L →ₗ[𝓞] (Fin d → ZMod p)) (C : Matrix (Fin d) (Fin d) (ZMod p)),
      Module.Free 𝓞 H₁.L ∧ Module.Finite 𝓞 H₁.L ∧ Module.finrank 𝓞 H₁.L = d ∧
      Function.Surjective lam₀ ∧
      (∀ m : H₁.L, lam₀ m = 0 → m ∈ Ideal.span {(p : 𝓞)} • (⊤ : Submodule 𝓞 H₁.L)) ∧
      IsNilpotent C ∧ (∀ m, lam₁ m = C.mulVec (lam₀ m)) ∧
      (∀ (l : H₁.L) (n : ℕ) (u : Deformation.wittHom (ZMod p) p (n + 1) Gc₁),
        Deformation.DieudonneModule.of (ZMod p) p Gc₁ (n + 1) u =
          Deformation.DieudonneModule.map (ZMod p) p qc₁ (π 1 ((l : H₁.L) : Fin r → 𝓞)) →
        ∀ f : MvPowerSeries (Fin d) (ZMod p), MvPowerSeries.constantCoeff f = 0 →
          κ₁ f = (u : TruncatedWittVector p (n + 1) Gc₁).coeff (Fin.last n) →
          ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) f = lam₀ l j) ∧
      (∀ (l : H₁.L) (n : ℕ) (u : Deformation.wittHom (ZMod p) p (n + 2) Gc₁),
        Deformation.DieudonneModule.of (ZMod p) p Gc₁ (n + 2) u =
          Deformation.DieudonneModule.map (ZMod p) p qc₁ (π 1 ((l : H₁.L) : Fin r → 𝓞)) →
        ∀ f : MvPowerSeries (Fin d) (ZMod p), MvPowerSeries.constantCoeff f = 0 →
          κ₁ f = (u : TruncatedWittVector p (n + 2) Gc₁).coeff ⟨n, by omega⟩ →
          ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) f = lam₁ l j) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq.solution
