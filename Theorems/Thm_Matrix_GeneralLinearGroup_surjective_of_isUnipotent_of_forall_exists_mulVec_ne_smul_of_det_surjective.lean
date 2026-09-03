import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_surjective_of_isUnipotent_of_forall_exists_mulVec_ne_smul_of_det_surjective

theorem Matrix.GeneralLinearGroup.surjective_of_isUnipotent_of_forall_exists_mulVec_ne_smul_of_det_surjective
    {G : Type*} [Group G] (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hunip : ∃ σ : G,
      (((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) - 1) ^ 2 = 0 ∧
        ((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1)
    (hirr : ∀ v : Fin 2 → ZMod 3, v ≠ 0 → ∃ σ : G, ∀ c : ZMod 3,
      Matrix.mulVec ((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) v
        ≠ c • v)
    (hdet : ∀ u : (ZMod 3)ˣ, ∃ σ : G, Matrix.GeneralLinearGroup.det (ρ σ) = u) :
    Function.Surjective ρ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_surjective_of_isUnipotent_of_forall_exists_mulVec_ne_smul_of_det_surjective.solution
