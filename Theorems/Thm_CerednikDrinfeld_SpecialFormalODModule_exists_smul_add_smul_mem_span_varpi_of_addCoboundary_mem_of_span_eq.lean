import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_span_eq

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_span_eq
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀,
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
      (∀ m ∈ X₀.toFormalODModule.lieOne j₀,
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)))
    (hI : Ideal.span (Set.range X₀.varpi) =
      Ideal.span ({MvPowerSeries.X 1, MvPowerSeries.X 0 ^ (q ^ 2)} : Set (MvPowerSeries (Fin 2) k)))
    (ψ : Zp2 q → k) (g g' : MvPowerSeries (Fin 2) k)
    (hg0 : MvPowerSeries.constantCoeff g = 0) (hg0' : MvPowerSeries.constantCoeff g' = 0)
    (hgP : X₀.F.addCoboundary g ∈ Ideal.span (Set.range (Sum.elim
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i))
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i)))))
    (hgP' : X₀.F.addCoboundary g' ∈ Ideal.span (Set.range (Sum.elim
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i))
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i)))))
    (hgT : ∀ a : Zp2 q, MvPowerSeries.subst (X₀.act a) g - ψ a • g ∈ Ideal.span (Set.range X₀.varpi))
    (hgT' : ∀ a : Zp2 q, MvPowerSeries.subst (X₀.act a) g' - ψ a • g' ∈ Ideal.span (Set.range X₀.varpi)) :
    ∃ c c' : k, (c ≠ 0 ∨ c' ≠ 0) ∧ c • g + c' • g' ∈ Ideal.span (Set.range X₀.varpi) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_span_eq.solution
