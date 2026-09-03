import Mathlib
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (θ : G →* G) {m : ℕ} (δ : Fin (m + 1) → G)
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] :
    ∃ (e : AutomorphicForm.sigmaCentralizer
            (MonoidHom.pi fun j : Fin (m + 1) =>
              Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ ≃ₜ*
          AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod)
      (X : G × (Fin m → G) ≃ₜ (Fin (m + 1) → G)),
      (∀ t, ((e t : AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod) : G) =
        (t : Fin (m + 1) → G) 0) ∧
      MeasurePreserving X (μ.prod (Measure.pi fun _ => μ)) (Measure.pi fun _ => μ) ∧
      (∀ p : G × (Fin m → G), X p 0 = p.1) ∧
      (∀ p : G × (Fin m → G),
        (X p)⁻¹ * δ *
            (MonoidHom.pi fun j : Fin (m + 1) =>
              Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) (X p) =
          Fin.snoc p.2 (((List.ofFn p.2).prod)⁻¹ * (p.1⁻¹ * (List.ofFn δ).prod * θ p.1))) ∧
      (∀ (t : AutomorphicForm.sigmaCentralizer
              (MonoidHom.pi fun j : Fin (m + 1) =>
                Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                  (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                  (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ)
          (p : G × (Fin m → G)),
        (t : Fin (m + 1) → G) * X p =
          X (((e t : AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod) : G) * p.1, p.2)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift.solution
