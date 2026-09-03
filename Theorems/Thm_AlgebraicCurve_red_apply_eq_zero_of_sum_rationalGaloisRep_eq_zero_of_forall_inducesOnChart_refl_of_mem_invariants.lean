import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_red_apply_eq_zero_of_sum_rationalGaloisRep_eq_zero_of_forall_inducesOnChart_refl_of_mem_invariants

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

theorem AlgebraicCurve.red_apply_eq_zero_of_sum_rationalGaloisRep_eq_zero_of_forall_inducesOnChart_refl_of_mem_invariants
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
    (i : Fin n) {T : Type} [Fintype T] [Nonempty T] (u : T → SemilinearAut L F)
    (huV : ∀ (t : T) (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)), v ∈ Vinv →
      ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) (u t) v ∈ Vinv)
    (hint : ∀ (t : T) (f : F), f ∈ (C i).integers ↔ u t • f ∈ (C i).integers)
    (hres : ∀ (t : T) (f : F) (hf : f ∈ (C i).integers),
      (C i).residue ⟨u t • f, (hint t f).mp hf⟩ = (C i).residue ⟨f, hf⟩)
    (hdom : ∀ (t : T) (P : Place L F), P ∈ (C i).dom ↔ u t • P ∈ (C i).dom)
    (hplace : ∀ (t : T), ∀ P ∈ (C i).dom, (C i).placeMap (u t • P) = (C i).placeMap P)
    (hperm : ∀ (t : T) (j : Fin n), ∃ j', ∀ P : Place L F, P ∈ (C j).dom → u t • P ∈ (C j').dom)
    (v : ↥Vinv)
    (hsum : ∑ t, ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) (u t)
      (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = 0) :
    red v i = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_red_apply_eq_zero_of_sum_rationalGaloisRep_eq_zero_of_forall_inducesOnChart_refl_of_mem_invariants.solution
