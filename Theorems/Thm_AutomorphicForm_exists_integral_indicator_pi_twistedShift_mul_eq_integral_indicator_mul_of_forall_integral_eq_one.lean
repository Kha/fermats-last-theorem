import Mathlib
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (θ : G →* G) (hθ : Continuous θ) {m : ℕ} (δ : Fin (m + 1) → G)
    (μ : Measure G) [μ.IsHaarMeasure]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hμU : μ U = 1)
    (τ : Measure (AutomorphicForm.sigmaCentralizer
        (MonoidHom.pi fun j : Fin (m + 1) =>
          Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
            (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
            (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ)) [SFinite τ]
    (w : (Fin (m + 1) → G) → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w) (hwc : HasCompactSupport w)
    (hsec : ∀ x : Fin (m + 1) → G,
      x⁻¹ * δ *
          (MonoidHom.pi fun j : Fin (m + 1) =>
            Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
              (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
              (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) x ∈
        Set.univ.pi (fun _ : Fin (m + 1) => (U : Set G)) →
      ∫ t : AutomorphicForm.sigmaCentralizer
          (MonoidHom.pi fun j : Fin (m + 1) =>
            Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
              (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
              (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ,
        w ((t : Fin (m + 1) → G) * x) ∂τ = 1) :
    ∃ (e : AutomorphicForm.sigmaCentralizer
            (MonoidHom.pi fun j : Fin (m + 1) =>
              Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ ≃ₜ*
          AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod)
      (s : G → ℝ),
      (∀ t, ((e t : AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod) : G) = (t : Fin (m + 1) → G) 0) ∧
      (∀ x, 0 ≤ s x) ∧ Measurable s ∧ HasCompactSupport s ∧
      (∀ x₀ : G, x₀⁻¹ * (List.ofFn δ).prod * θ x₀ ∈ U →
        ∫ t : AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod, s ((t : G) * x₀) ∂(Measure.map e τ) = 1) ∧
      (Integrable (fun x : Fin (m + 1) → G =>
          (Set.univ.pi fun _ : Fin (m + 1) => (U : Set G)).indicator (fun _ => (1 : ℂ))
            (x⁻¹ * δ *
              (MonoidHom.pi fun j : Fin (m + 1) =>
                Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                  (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                  (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) x) *
            (w x : ℂ)) (Measure.pi fun _ => μ) →
        ∫ x : Fin (m + 1) → G,
            (Set.univ.pi fun _ : Fin (m + 1) => (U : Set G)).indicator (fun _ => (1 : ℂ))
              (x⁻¹ * δ *
                (MonoidHom.pi fun j : Fin (m + 1) =>
                  Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                    (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                    (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) x) *
              (w x : ℂ) ∂(Measure.pi fun _ => μ) =
          ∫ x₀ : G, (U : Set G).indicator (fun _ => (1 : ℂ)) (x₀⁻¹ * (List.ofFn δ).prod * θ x₀) * (s x₀ : ℂ) ∂μ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_integral_indicator_pi_twistedShift_mul_eq_integral_indicator_mul_of_forall_integral_eq_one.solution
