import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_heckeAlg_tower_smul_smul_eq_and_smul_eq_iff_mem_eisensteinPrimaryTorsionBar

open ModularCurve

theorem ModularCurve.exists_heckeAlg_tower_smul_smul_eq_and_smul_eq_iff_mem_eisensteinPrimaryTorsionBar
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hfin : ∀ m : ℕ, Finite ↥(jZeroTorsion p (q ^ m))) :
    letI := heckeModuleBar p
    ∃ t : ℕ → HeckeAlg, ∀ (m : ℕ) (x : JZero p), (q ^ m : ℤ) • x = 0 →
      t m • (t m • x) = t m • x ∧ (t m • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m) ∧
        t (m + 1) • x = t m • x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_heckeAlg_tower_smul_smul_eq_and_smul_eq_iff_mem_eisensteinPrimaryTorsionBar.solution
