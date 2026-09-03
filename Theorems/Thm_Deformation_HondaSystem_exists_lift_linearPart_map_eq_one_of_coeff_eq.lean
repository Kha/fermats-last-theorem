import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_exists_lift_linearPart_map_eq_one_of_coeff_eq

universe u

theorem Deformation.HondaSystem.exists_lift_linearPart_map_eq_one_of_coeff_eq
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (abar : Fin d → ℕ → MvPowerSeries (Fin d) (ZMod p))
    (habar : ∀ i n, MvPowerSeries.constantCoeff (abar i n) = 0)
    (h0 : ∀ i j : Fin d, MvPowerSeries.coeff (Finsupp.single j 1) (abar i 0) = if i = j then 1 else 0)
    (h1 : ∀ i j : Fin d, j ≤ i → MvPowerSeries.coeff (Finsupp.single j 1) (abar i 1) = 0) :
    ∃ a : Fin d → ℕ → MvPowerSeries (Fin d) 𝓞,
      (∀ i n, MvPowerSeries.map (algebraMap 𝓞 (ZMod p)) (a i n) = abar i n) ∧
      (∀ i n, MvPowerSeries.constantCoeff (a i n) = 0) ∧
      IsUnit ((MvFormalGroup.linearPart fun i => a i 0).map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))) ∧
      ((MvFormalGroup.linearPart fun i => a i 0).map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)})) = 1 ∧
        ∀ i j : Fin d, j ≤ i → MvFormalGroup.linearPart (fun i => a i 1) i j ∈ Ideal.span {(p : 𝓞)}) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_exists_lift_linearPart_map_eq_one_of_coeff_eq.solution
