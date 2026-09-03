import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hnode₀ : ∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (hnode₁ : ∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (γ : MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hγ : X₀.F.IsSymmTwoCocycle γ)
    (g : MvPowerSeries (Fin 2) k) (hg0 : MvPowerSeries.constantCoeff g = 0)
    (hglin : ∀ m, MvPowerSeries.coeff (Finsupp.single m 1) g = 0) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    pull X₀.varpi γ = X₀.F.addCoboundary g →
    ∃ b : MvPowerSeries (Fin 2) k, MvPowerSeries.constantCoeff b = 0 ∧ γ = X₀.F.addCoboundary b := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_eq_addCoboundary_of_subst_varpi_eq_addCoboundary_of_coeff_eq_zero.solution
