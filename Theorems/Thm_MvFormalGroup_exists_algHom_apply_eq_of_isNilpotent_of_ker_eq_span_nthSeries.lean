import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_algHom_apply_eq_of_isNilpotent_of_ker_eq_span_nthSeries

open MvPowerSeries

universe u v w

theorem MvFormalGroup.exists_algHom_apply_eq_of_isNilpotent_of_ker_eq_span_nthSeries (p : ℕ) [Fact p.Prime] {d : ℕ}
    (Φ₀ : MvFormalGroup d (ZMod p)) [Φ₀.IsComm]
    {Gc : ℕ → Type v} [∀ v, CommRing (Gc v)] [∀ v, Algebra (ZMod p) (Gc v)]
    (κ : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] Gc v) (hκ : ∀ v, Function.Surjective (κ v))
    (hker : ∀ v, RingHom.ker (κ v) = Ideal.span (Set.range (Φ₀.nthSeries (p ^ v))))
    {S : Type w} [CommRing S] [Algebra (ZMod p) S] (x : Fin d → S) (hx : ∀ i, IsNilpotent (x i)) :
    ∃ (v : ℕ) (f : Gc v →ₐ[ZMod p] S), ∀ i, f (κ v (X i)) = x i := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_algHom_apply_eq_of_isNilpotent_of_ker_eq_span_nthSeries.solution
