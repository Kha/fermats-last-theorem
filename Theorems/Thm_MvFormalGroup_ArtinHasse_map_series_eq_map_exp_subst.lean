import Mathlib
import Definitions.Def_MvFormalGroup_ArtinHasse
import P2M.Util
import P2M.Sol.S_MvFormalGroup_ArtinHasse_map_series_eq_map_exp_subst

set_option autoImplicit false

open Classical in

theorem MvFormalGroup.ArtinHasse.map_series_eq_map_exp_subst (p : ℕ) [Fact p.Prime] :
    PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (MvFormalGroup.ArtinHasse.series p) =
      PowerSeries.map (algebraMap ℚ ℚ_[p])
        ((PowerSeries.exp ℚ).subst
          (PowerSeries.mk fun k : ℕ => if ∃ m : ℕ, k = p ^ m then (k : ℚ)⁻¹ else 0)) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_ArtinHasse_map_series_eq_map_exp_subst.solution
