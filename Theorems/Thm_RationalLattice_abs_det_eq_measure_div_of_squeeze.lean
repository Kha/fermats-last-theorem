import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_RationalLattice_abs_det_eq_measure_div_of_squeeze

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory

theorem RationalLattice.abs_det_eq_measure_div_of_squeeze [MeasurableSpace (Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ)]
    [BorelSpace (Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ)] (U : AddSubgroup (Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (N N' : ℕ)
    (hN : 0 < N) (hN' : 0 < N')
    (hlow : ∀ z : Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ i, z i ∈ (fun w => (N : FiniteAdeleRing (𝓞 ℚ) ℚ) * w) '' AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ) → z ∈ U)
    (hup : ∀ u ∈ U, ∀ i, (N' : FiniteAdeleRing (𝓞 ℚ) ℚ) * u i ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ)
    (μ : Measure (Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ)) [μ.IsAddHaarMeasure] (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : (fun ξ : Fin 3 → ℚ => WithLp.toLp 2 fun i => (ξ i : ℝ)) ''
        {ξ : Fin 3 → ℚ | (fun i => algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ i)) ∈ U} =
      Set.range fun n : Fin 3 → ℤ => WithLp.toLp 2 (B.mulVec fun i => (n i : ℝ))) :
    |B.det| = (μ (Set.pi Set.univ fun _ => AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ) / μ U).toReal := by p2m_exact_reverting @_root_.P2MW.S_RationalLattice_abs_det_eq_measure_div_of_squeeze.solution
