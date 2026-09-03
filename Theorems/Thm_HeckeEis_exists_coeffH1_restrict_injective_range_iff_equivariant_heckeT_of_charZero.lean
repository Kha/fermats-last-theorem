import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_coeffH1_restrict_injective_range_iff_equivariant_heckeT_of_charZero

set_option autoImplicit false

open CongruenceSubgroup

theorem HeckeEis.exists_coeffH1_restrict_injective_range_iff_equivariant_heckeT_of_charZero
    (N q : ℕ) [Fact q.Prime] (K : Type) [Field K] [CharZero K]
    {Wc : Type} [AddCommGroup Wc] [Module K Wc] (W : Representation K (CuspidalType.GL2 q) Wc)
    (red : Gamma0 N →* CuspidalType.GL2 q)
    (hred : red = (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)
    (H₁ : Subgroup (ZMod (N * q ^ 2))ˣ)
    (hH₁ : H₁ = (ZMod.unitsMap ((dvd_pow_self q two_ne_zero).mul_left N)).ker)
    (conj : ↥red.ker →* ↥(CohCarrier.GammaH (N * q ^ 2) H₁))
    (hconj : ∀ x : ↥red.ker,
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 = ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 ∧
      (q : ℤ) * (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 =
        ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 ∧
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 =
        (q : ℤ) * ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 ∧
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 =
        ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1) :
    ∃ S : HeckeEis.coeffH1 (W.comp red) →ₗ[K] CohCarrier.H1 (N * q ^ 2) H₁ Wc,
      (∀ (z : ↥(HeckeEis.coeffCocycles (W.comp red))) (x : ↥red.ker),
        S (HeckeEis.coeffH1Mk (W.comp red) z) (Additive.ofMul (conj x)) = (z : Gamma0 N → Wc) (x : Gamma0 N)) ∧
      Function.Injective S ∧
      (∀ φ : CohCarrier.H1 (N * q ^ 2) H₁ Wc, φ ∈ LinearMap.range S ↔
        ∀ (γ y : Gamma0 N) (hy : y ∈ red.ker) (hy' : γ * y * γ⁻¹ ∈ red.ker),
          φ (Additive.ofMul (conj ⟨γ * y * γ⁻¹, hy'⟩)) = W (red γ) (φ (Additive.ofMul (conj ⟨y, hy⟩)))) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ], Nat.Coprime ℓ (N * q) → ∀ h : ((ℓ : ZMod q) ≠ 0),
        ∃ T : HeckeEis.coeffH1 (W.comp red) →ₗ[K] HeckeEis.coeffH1 (W.comp red),
          HeckeEis.IsCoeffHeckeOnH1 N ℓ (W.comp red) (W (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))) T ∧
          ∀ x : HeckeEis.coeffH1 (W.comp red),
            S (T x) = (W (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))).toAddMonoidHom.comp
              (CohCarrier.heckeT (N * q ^ 2) H₁ ℓ Wc (S x)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_coeffH1_restrict_injective_range_iff_equivariant_heckeT_of_charZero.solution
