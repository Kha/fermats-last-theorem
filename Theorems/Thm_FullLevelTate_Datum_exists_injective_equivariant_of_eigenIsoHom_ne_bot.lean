import Definitions.Def_FullLevelTate_IsoHom
import P2M.Util
import P2M.Sol.S_FullLevelTate_Datum_exists_injective_equivariant_of_eigenIsoHom_ne_bot
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

theorem FullLevelTate.Datum.exists_injective_equivariant_of_eigenIsoHom_ne_bot
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (O' : Type) [CommRing O'] [IsLocalRing O'] [IsNoetherianRing O']
    (D : FullLevelTate.Datum q M' O')
    (K : Type) [Field K] [CharZero K] [Algebra O' K] (hOK : Function.Injective (algebraMap O' K))
    {H : Subgroup (CuspidalType.GL2 q)} {W : Type} [AddCommGroup W] [Module K W] (χ : Representation K H W)
    (hcentral : ∀ c : (ZMod q)ˣ, ∃ h : H, (h : CuspidalType.GL2 q) = CuspidalType.scalarElem q c ∧ χ h = 1)
    (hk : ModularCurve.HeckeAlg →+* K) (hne : D.eigenIsoHom K χ hk ≠ ⊥)
    (S : Finset ℕ) (ρ : GaloisRepAdic O')
    (hρ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q → ¬ ℓ ∣ M' → ℓ ∉ (↑S : Set ℕ) →
      (ℓ : O') ∉ IsLocalRing.maximalIdeal O' →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt s ℓ →
          (LinearMap.charpoly (ρ.ρ s)).map (algebraMap O' K) =
            X ^ 2 - C (hk (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)) * X + C ((ℓ : K)))
    (hirr : ∀ U : Submodule K (K ⊗[O'] ρ.V),
      (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ v ∈ U, (ρ.ρ s).baseChange K v ∈ U) →
        U = ⊥ ∨ U = ⊤)
    (hodd : ∃ c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ρ.ρ c * ρ.ρ c = 1 ∧ LinearMap.det (ρ.ρ c) = -1) :
    ∃ φ : K ⊗[O'] ρ.V →ₗ[K] D.eigenIsoHom K χ hk,
      Function.Injective φ ∧
        ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          φ ∘ₗ (ρ.ρ s).baseChange K = D.eigenIsoHomGal K χ hk s ∘ₗ φ := by p2m_exact_reverting @_root_.P2MW.S_FullLevelTate_Datum_exists_injective_equivariant_of_eigenIsoHom_ne_bot.solution
