import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_forall_point_valuation_cartierTranspose_sub_pow_lt_one_of_comp_eq_comp_verschiebung_of_bijective_tensorProduct_zmodp
attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions
attribute [-simp] HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff

set_option autoImplicit false

open scoped TensorProduct
open IsLocalRing

theorem PDivisibleGroup.CartierDuality.forall_point_valuation_cartierTranspose_sub_pow_lt_one_of_comp_eq_comp_verschiebung_of_bijective_tensorProduct_zmodp
    (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    {h : ℕ} (𝒢 : PDivisibleGroup Rh p h) {𝒢' : PDivisibleGroup Rh p h} (Dual : 𝒢.CartierDuality 𝒢')
    (v : ℕ)

    (f ε : 𝒢.level v →ₐc[Rh] 𝒢.level v)

    (VB : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v)
    (hVB : ∀ (φ : CartierDual (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v)) (b : ZMod p ⊗[Rh] 𝒢.level v),
      φ (VB b) = (φ ^ p) b)

    (Gc : Type) [CommRing Gc] [HopfAlgebra (ZMod p) Gc] [Coalgebra.IsCocomm (ZMod p) Gc] [Module.Finite (ZMod p) Gc]
    (Ge : Type) [CommRing Ge] [HopfAlgebra (ZMod p) Ge] [Coalgebra.IsCocomm (ZMod p) Ge] [Module.Finite (ZMod p) Ge]
    (qc : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] Gc) (πe : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] Ge)
    (Θ : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] Gc ⊗[ZMod p] Ge)
    (hGc : IsLocalRing Gc) (hGe : IsReduced Ge)
    (hqc : Function.Surjective qc) (hπe : Function.Surjective πe) (hΘ : Function.Bijective Θ)
    (hΘΔ : ∀ b, Θ b = Algebra.TensorProduct.map (qc : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Gc)
      (πe : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Ge) (Coalgebra.comul (R := ZMod p) b))

    (hV : (qc : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Gc).comp
        (((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) f).comp
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ε) :
            ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) :
          ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) =
      (qc : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Gc).comp
        ((VB.comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ε) :
            ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) :
          ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v)) :
    ∀ ψ : 𝒢'.Point (AlgebraicClosure ℚ) v,

      (∀ a : 𝒢'.level v, PDivisibleGroup.Point.toAlgHom ψ a ∈ Pl) →

      (PDivisibleGroup.Point.toAlgHom ψ).comp (((Dual.equiv v).symm : CartierDual Rh (𝒢.level v) →ₐc[Rh] 𝒢'.level v).comp
          ((CartierDual.map ε).comp (Dual.equiv v : 𝒢'.level v →ₐc[Rh] CartierDual Rh (𝒢.level v))) :
            𝒢'.level v →ₐ[Rh] 𝒢'.level v) = PDivisibleGroup.Point.toAlgHom ψ →

      ∀ a : 𝒢'.level v,
        Pl.valuation ((PDivisibleGroup.Point.toAlgHom ψ).comp (((Dual.equiv v).symm : CartierDual Rh (𝒢.level v) →ₐc[Rh] 𝒢'.level v).comp
          ((CartierDual.map f).comp (Dual.equiv v : 𝒢'.level v →ₐc[Rh] CartierDual Rh (𝒢.level v))) :
            𝒢'.level v →ₐ[Rh] 𝒢'.level v) a -
          PDivisibleGroup.Point.toAlgHom ψ a ^ p) < 1 := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_forall_point_valuation_cartierTranspose_sub_pow_lt_one_of_comp_eq_comp_verschiebung_of_bijective_tensorProduct_zmodp.solution
