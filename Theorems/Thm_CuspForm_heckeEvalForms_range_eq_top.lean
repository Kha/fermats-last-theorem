import Definitions.Def_CuspForm_HeckeEvalForms
import P2M.Util
import P2M.Sol.S_CuspForm_heckeEvalForms_range_eq_top

theorem CuspForm.heckeEvalForms_range_eq_top (N : ℕ) [NeZero N] (k : ℤ) : (CuspForm.heckeEvalForms N k).range = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeEvalForms_range_eq_top.solution
