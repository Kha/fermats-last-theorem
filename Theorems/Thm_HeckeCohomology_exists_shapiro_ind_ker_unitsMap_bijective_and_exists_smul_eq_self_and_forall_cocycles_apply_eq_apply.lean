import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_DClassCoeff
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import P2M.Util
import P2M.Sol.S_HeckeCohomology_exists_shapiro_ind_ker_unitsMap_bijective_and_exists_smul_eq_self_and_forall_cocycles_apply_eq_apply

set_option autoImplicit false

open scoped CuspidalType in

theorem
HeckeCohomology.exists_shapiro_ind_ker_unitsMap_bijective_and_exists_smul_eq_self_and_forall_cocycles_apply_eq_apply
    (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (hqN : ¬ q ∣ N) (κ : Type) [Field κ]
    (lift : CongruenceSubgroup.Gamma0 (N * q) → CongruenceSubgroup.Gamma0 N)
    (hlift : ∀ σ, ((lift σ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
      (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    ∃ Φ : groupCohomology.H1
        (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
          ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype)))) →+
        CohCarrier.H1 (N * q) (ZMod.unitsMap (dvd_mul_right N q)).ker κ,
      Function.Bijective Φ ∧
      (∀ (c : κ) x, Φ (c • x) = c • Φ x) ∧
      ∃ x₀ : CuspidalType.ProjLine q,
        (∀ γ : ↥(CohCarrier.GammaH (N * q) (ZMod.unitsMap (dvd_mul_right N q)).ker),
          Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))
            (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) • x₀ = x₀) ∧
        ∀ (f : groupCohomology.cocycles₁
              (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
                ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype)))))
          (γ : ↥(CohCarrier.GammaH (N * q) (ZMod.unitsMap (dvd_mul_right N q)).ker))
          (h : (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ CohCarrier.GammaH N ⊥),
          Φ (groupCohomology.H1π
              (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
                ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype))))
            f) (Additive.ofMul γ) =
            (f ⟨(γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), h⟩ : CuspidalType.ProjLine q →₀ κ) x₀ := by p2m_exact_reverting @_root_.P2MW.S_HeckeCohomology_exists_shapiro_ind_ker_unitsMap_bijective_and_exists_smul_eq_self_and_forall_cocycles_apply_eq_apply.solution
