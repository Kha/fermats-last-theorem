import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

theorem AlgebraicCurve.red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (F : Type) [Field F] [Algebra L F]
    (n : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (C : ∀ i, ComponentChart A F (Fbar i))

    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Vinv : Submodule ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F)))
    (red : ↥Vinv →ₗ[ℚ_[ℓ]] ∀ i, ModularCurve.RationalTateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)))
    (hred : ∀ (v : ↥Vinv) (x : TateModule ℓ (Pic0 L F)),
      (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ (k : ℕ) (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)),
      Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x →
      ∀ Di : Fin n → Divisor L F, D = ∑ i, Di i → (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) →
        (∀ i, Divisor.degree (Di i) = 0) →
        ∀ i, ∃ y : TateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)),
          red v i = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y ∧
          ∀ E : Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i),
            (E : Divisor (IsLocalRing.ResidueField A) (Fbar i)) =
                Finsupp.mapDomain (C i).placeMap (Di i) →
              TateModule.proj ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k y = Pic0.mk E)

    (hrep : ∀ (v : ↥Vinv) (x : TateModule ℓ (Pic0 L F)),
      (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ k : ℕ, ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (Di : Fin n → Divisor L F),
        Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x ∧
        D = ∑ i, Di i ∧ (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0)
    (g : SemilinearAut L F)
    (hgV : ∀ v : ModularCurve.RationalTateModule ℓ (Pic0 L F), v ∈ Vinv →
      ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g v ∈ Vinv)
    (i : Fin n) (φ : Fbar i ≃ₐ[IsLocalRing.ResidueField A] Fbar i)
    (hint : ∀ f : F, f ∈ (C i).integers ↔ g • f ∈ (C i).integers)
    (hres : ∀ (f : F) (hf : f ∈ (C i).integers), (C i).residue ⟨g • f, (hint f).mp hf⟩ = φ ((C i).residue ⟨f, hf⟩))
    (hdom : ∀ P : Place L F, P ∈ (C i).dom ↔ g • P ∈ (C i).dom)
    (hplace : ∀ P ∈ (C i).dom, (C i).placeMap (g • P) = SemilinearAut.ofAlgAut φ • (C i).placeMap P)
    (hperm : ∀ j, ∃ j', ∀ P : Place L F, P ∈ (C j).dom → g • P ∈ (C j').dom)
    (v : ↥Vinv) :
    red ⟨ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g v, hgV v v.2⟩ i =
      ModularCurve.rationalGaloisRep ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i))
        (Fbar i ≃ₐ[IsLocalRing.ResidueField A] Fbar i) φ (red v i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants.solution
