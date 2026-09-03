import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient
attribute [-instance] PDivisibleGroup.Points.instAddCommGroup PDivisibleGroup.Points.instInhabited PDivisibleGroup.Point.instCommGroup PDivisibleGroup.pointsDirectedSystem PDivisibleGroup.Points.instDistribMulAction PDivisibleGroup.Point.instCommMonoid TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] PDivisibleGroup.Points.smul_pointsMkAdd PDivisibleGroup.pointsMkAdd_pointInclLE PDivisibleGroup.Point.toAlgHom_ofAlgHom PDivisibleGroup.pointsMkAdd_pointIncl PDivisibleGroup.pointsMk_pointInclLE PDivisibleGroup.pointIncl_apply PDivisibleGroup.pointInclLE_self PDivisibleGroup.toAlgHom_pointMap PDivisibleGroup.Point.toConv_ofConv PDivisibleGroup.Hopf.antipodeAlgHom_apply PDivisibleGroup.Hopf.convCompMonoidHom_apply PDivisibleGroup.pointsMap_pointsMkAdd PDivisibleGroup.Point.ofAlgHom_toAlgHom PDivisibleGroup.pointsMk_pointIncl PDivisibleGroup.Point.ofConv_toConv TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (ZMod p)]
    {h : ℕ} (𝒢 : PDivisibleGroup O p h)
    (φ : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v) (Dp : ∀ v : ℕ, 𝒢.level v ≃ₐc[O] 𝒢.level v)
    (hφt : ∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v))
    (hDpt : ∀ v : ℕ, (𝒢.transition v).comp (Dp (v + 1) : 𝒢.level (v + 1) →ₐc[O] 𝒢.level (v + 1)) =
      (Dp v : 𝒢.level v →ₐc[O] 𝒢.level v).comp (𝒢.transition v))

    {hT : ℕ} (T : ℕ → Type) [∀ v, CommRing (T v)] [∀ v, HopfAlgebra (ZMod p) (T v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (T v)] [∀ v, Module.Finite (ZMod p) (T v)]
    [∀ v, Module.Free (ZMod p) (T v)]
    (tT : ∀ v, T (v + 1) →ₐc[ZMod p] T v) (htT : ∀ v, Function.Surjective (tT v))
    (hrankT : ∀ v, Module.finrank (ZMod p) (T v) = p ^ (v * hT))
    (hkerT : ∀ v, RingHom.ker (tT v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (T (v + 1)) (p ^ v))
    (πT : ∀ v : ℕ, ZMod p ⊗[O] 𝒢.level v →ₐc[ZMod p] T v) (hπT : ∀ v, Function.Surjective (πT v))
    (hπTt : ∀ v : ℕ, (πT v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) = (tT v).comp (πT (v + 1)))
    (VerT : ∀ v : ℕ, T v ≃ₐc[ZMod p] T v)
    (hVerT : ∀ (v : ℕ) (ψ : CartierDual (ZMod p) (T v)), CartierDual.map (VerT v : T v →ₐc[ZMod p] T v) ψ = ψ ^ p)

    {hB : ℕ} (Bq : ℕ → Type) [∀ v, CommRing (Bq v)] [∀ v, HopfAlgebra (ZMod p) (Bq v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (Bq v)] [∀ v, Module.Finite (ZMod p) (Bq v)]
    [∀ v, Module.Free (ZMod p) (Bq v)]
    (tB : ∀ v, Bq (v + 1) →ₐc[ZMod p] Bq v) (htB : ∀ v, Function.Surjective (tB v))
    (hrankBq : ∀ v, Module.finrank (ZMod p) (Bq v) = p ^ (v * hB))
    (hkerBq : ∀ v, RingHom.ker (tB v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Bq (v + 1)) (p ^ v))
    (jB : ∀ v : ℕ, Bq v →ₐc[ZMod p] ZMod p ⊗[O] 𝒢.level v) (hjB : ∀ v, Function.Injective (jB v))
    (hjBt : ∀ v : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)).comp (jB (v + 1)) = (jB v).comp (tB v))
    (hexT : ∀ v : ℕ, RingHom.ker (πT v : ZMod p ⊗[O] 𝒢.level v →ₐ[ZMod p] T v) =
      Ideal.map (jB v : Bq v →ₐ[ZMod p] ZMod p ⊗[O] 𝒢.level v) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (Bq v))))

    (hπTφ : ∀ v : ℕ, ∃ uT : T v →ₐc[ZMod p] T v, (πT v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (φ v)) = uT.comp (πT v))
    (hπTD : ∀ v : ℕ, ∃ eT : T v →ₐc[ZMod p] T v,
      (πT v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (Dp v : 𝒢.level v →ₐc[O] 𝒢.level v)) = eT.comp (πT v))
    (φB : ∀ v : ℕ, Bq v →ₐc[ZMod p] Bq v) (DB : ∀ v : ℕ, Bq v ≃ₐc[ZMod p] Bq v)
    (hjBφ : ∀ v : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (φ v)).comp (jB v) = (jB v).comp (φB v))
    (hjBD : ∀ v : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p))
        (Dp v : 𝒢.level v →ₐc[O] 𝒢.level v)).comp (jB v) = (jB v).comp (DB v : Bq v →ₐc[ZMod p] Bq v))

    {h₁ : ℕ} (G₁ : ℕ → Type) [∀ v, CommRing (G₁ v)] [∀ v, HopfAlgebra (ZMod p) (G₁ v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G₁ v)] [∀ v, Module.Finite (ZMod p) (G₁ v)]
    [∀ v, Module.Free (ZMod p) (G₁ v)]
    (t₁ : ∀ v, G₁ (v + 1) →ₐc[ZMod p] G₁ v) (ht₁ : ∀ v, Function.Surjective (t₁ v))
    (hrankG₁ : ∀ v, Module.finrank (ZMod p) (G₁ v) = p ^ (v * h₁))
    (hkerG₁ : ∀ v, RingHom.ker (t₁ v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G₁ (v + 1)) (p ^ v))
    (π₁ : ∀ v : ℕ, Bq v →ₐc[ZMod p] G₁ v) (hπ₁ : ∀ v, Function.Surjective (π₁ v))
    (hπ₁t : ∀ v : ℕ, (π₁ v).comp (tB v) = (t₁ v).comp (π₁ (v + 1)))

    {h₂ : ℕ} (G₂ : ℕ → Type) [∀ v, CommRing (G₂ v)] [∀ v, HopfAlgebra (ZMod p) (G₂ v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G₂ v)] [∀ v, Module.Finite (ZMod p) (G₂ v)]
    [∀ v, Module.Free (ZMod p) (G₂ v)]
    (t₂ : ∀ v, G₂ (v + 1) →ₐc[ZMod p] G₂ v) (ht₂ : ∀ v, Function.Surjective (t₂ v))
    (hrankG₂ : ∀ v, Module.finrank (ZMod p) (G₂ v) = p ^ (v * h₂))
    (hkerG₂ : ∀ v, RingHom.ker (t₂ v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G₂ (v + 1)) (p ^ v))
    (j₂ : ∀ v : ℕ, G₂ v →ₐc[ZMod p] Bq v) (hj₂ : ∀ v, Function.Injective (j₂ v))
    (hj₂t : ∀ v : ℕ, (tB v).comp (j₂ (v + 1)) = (j₂ v).comp (t₂ v))
    (hex : ∀ v : ℕ, RingHom.ker (π₁ v : Bq v →ₐ[ZMod p] G₁ v) =
      Ideal.map (j₂ v : G₂ v →ₐ[ZMod p] Bq v) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (G₂ v))))

    (φ₁ : ∀ v : ℕ, G₁ v →ₐc[ZMod p] G₁ v) (φ₂ : ∀ v : ℕ, G₂ v →ₐc[ZMod p] G₂ v) (d₂ : ∀ v : ℕ, G₂ v ≃ₐc[ZMod p] G₂ v)
    (hπφ : ∀ v : ℕ, (π₁ v).comp (φB v) = (φ₁ v).comp (π₁ v))
    (hjφ : ∀ v : ℕ, (φB v).comp (j₂ v) = (j₂ v).comp (φ₂ v))
    (hjD : ∀ v : ℕ, (DB v : Bq v →ₐc[ZMod p] Bq v).comp (j₂ v) = (j₂ v).comp (d₂ v : G₂ v →ₐc[ZMod p] G₂ v))

    (Ver₁ : ∀ v : ℕ, G₁ v →ₐc[ZMod p] G₁ v)
    (hVer₁ : ∀ (v : ℕ) (ψ : CartierDual (ZMod p) (G₁ v)), CartierDual.map (Ver₁ v) ψ = ψ ^ p)

    (hE1 : ∀ v : ℕ, φ₁ v = Ver₁ v)

    (hE2 : ∀ (v : ℕ) (x : G₂ v), φ₂ v x = (d₂ v) (x ^ p)) :
    (∀ Fk : ZMod p ⊗[O] 𝒢.level 1 →ₐc[ZMod p] ZMod p ⊗[O] 𝒢.level 1, (∀ x, Fk x = x ^ p) →
          ∀ FD : CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₐ[ZMod p]
              CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1), (∀ ψ, FD ψ = ψ ^ p) →
          ∃ (n : ℕ) (a b : CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₐc[ZMod p]
              CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1)),
            (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (φ 1)) :
                CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₗ[ZMod p]
                  CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1)) ^ n =
              (WithConv.toConv ((FD : CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₗ[ZMod p]
                    CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1)) ∘ₗ
                  (a : CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₗ[ZMod p]
                    CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1))) *
                WithConv.toConv ((b : CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₗ[ZMod p]
                    CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1)) ∘ₗ
                  (CartierDual.map Fk : CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₗ[ZMod p]
                    CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1)))).ofConv) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient.solution
