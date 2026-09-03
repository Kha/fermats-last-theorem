import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_M4aHerbrand_nonempty_tate_addEquiv_ideleClass

set_option autoImplicit false
set_option maxSynthPendingDepth 3
universe u v w
theorem M4aHerbrand.nonempty_tate_addEquiv_ideleClass
    {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra E F] [Fintype (F ≃ₐ[E] F)]
    (D : M4aHerbrand.IdeleGaloisDescent R E F) (σ : F ≃ₐ[E] F) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
    [MulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : M4aHerbrand.IdeleClassGroup R F), g • c = D.classAct g c) :
    Nonempty ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)).tateH0 ≃+
      Additive ((M4aHerbrand.ideleClassDerive D σ).ker ⧸
        (M4aHerbrand.ideleClassNorm D).range.subgroupOf (M4aHerbrand.ideleClassDerive D σ).ker)) ∧
    Nonempty ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)).tateHneg1 ≃+
      Additive ((M4aHerbrand.ideleClassNorm D).ker ⧸
        (M4aHerbrand.ideleClassDerive D σ).range.subgroupOf (M4aHerbrand.ideleClassNorm D).ker)) ∧
    Nat.card (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)).tateH0 = Nat.card ((M4aHerbrand.ideleClassDerive D σ).ker ⧸
        (M4aHerbrand.ideleClassNorm D).range.subgroupOf (M4aHerbrand.ideleClassDerive D σ).ker) ∧
    Nat.card (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)).tateHneg1 = Nat.card ((M4aHerbrand.ideleClassNorm D).ker ⧸
        (M4aHerbrand.ideleClassDerive D σ).range.subgroupOf (M4aHerbrand.ideleClassNorm D).ker) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_nonempty_tate_addEquiv_ideleClass.solution
