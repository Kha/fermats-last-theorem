import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_pi_surj_torsion

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem solution
    {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) {n : ℕ} (hn : 0 < n) :
    ∀ t : P.JacPoints, n • t = 0 → ∃ u : ↥P.U, P.π u = t := by
  intro t ht
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective P.periodLattice t
  have hs : s ∈ P.U := by
    simp only [PeriodDatum.U, Submodule.mem_comap]
    refine (Submodule.mem_torsion_iff _).mpr
      ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    show (n : ℤ) • P.periodLattice.mkQ s = 0
    rw [natCast_zsmul]
    exact ht
  exact ⟨⟨s, hs⟩, rfl⟩
