import Mathlib
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_HeckeEis_isEigensystemH1_one_mul_of_isEigensystemH1_ind_comp

set_option autoImplicit false

open CongruenceSubgroup

theorem HeckeEis.isEigensystemH1_one_mul_of_isEigensystemH1_ind_comp
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ)
    (κ : Type) [Field κ] (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((CuspidalType.ind q κ).comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
      (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then (CuspidalType.ind q κ) (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))
        else LinearMap.id) S₀ lam) :
    haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
    HeckeEis.IsEigensystemH1 (N * q) (1 : Representation κ (Gamma0 (N * q)) κ) (fun _ => LinearMap.id)
      (insert q S₀) lam := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_isEigensystemH1_one_mul_of_isEigensystemH1_ind_comp.solution
