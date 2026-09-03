import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isCompact_and_exists_torusEmb_and_exists_tableMap_apply_eq_of_sq_eq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ComplexConjugate

theorem AutomorphicForm.isCompact_and_exists_torusEmb_and_exists_tableMap_apply_eq_of_sq_eq
    (L : Type) [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ))
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (d : ℕ) (w' : Fin d → HeightOneSpectrum (𝓞 L)) (hw'S : ∀ i : Fin d, w' i ∉ SL)
    (hw'i : Function.Injective w')
    (s : Fin d → ℂ)
    (hs : ∀ i : Fin d, s i ^ 2 =
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) :
    IsCompact (Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
      fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))) ∧
    (∃ emb : C((Fin d → AddCircle (1 : ℝ)), ↥(Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
        fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ))))),
      ∀ (θ : Fin d → AddCircle (1 : ℝ)) (i : Fin d),
        ((emb θ : ↥(Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
          fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ))))) : Fin d → ℂ × ℂ) i =
          ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ))) ∧
    (∀ i : Fin d, Continuous (fun p : ℂ × ℂ =>
      (((Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ) * s i * (p.1 + p.2),
        HeckeEigensystem.cNorm (w' i) *
            ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) +
          (p.1 * p.2 - 1)) : ℂ × ℂ))) ∧
    (∀ (i : Fin d) (q : ℂ × ℂ), ((fun p : ℂ × ℂ =>
      (((Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ) * s i * (p.1 + p.2),
        HeckeEigensystem.cNorm (w' i) *
            ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) +
          (p.1 * p.2 - 1)) : ℂ × ℂ)) ⁻¹' {q}).Finite) ∧
    ∃ bc : C(↥(Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
        fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))), X),
      ∀ (x : ↥(Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
          fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ))))) (i : Fin d),
        ((bc x : X) : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' i) =
          ((Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ) * s i *
              (((x : Fin d → ℂ × ℂ) i).1 + ((x : Fin d → ℂ × ℂ) i).2),
            HeckeEigensystem.cNorm (w' i) *
                ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) +
              (((x : Fin d → ℂ × ℂ) i).1 * ((x : Fin d → ℂ × ℂ) i).2 - 1)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isCompact_and_exists_torusEmb_and_exists_tableMap_apply_eq_of_sq_eq.solution
