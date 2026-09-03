import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SiegelCovering
import P2M.Util
namespace P2MW.S_AutomorphicForm_eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero

set_option autoImplicit false

open NumberField AutomorphicForm AutomorphicForm.SiegelCovering

theorem solution
    (F : Type) [Field F] [NumberField F]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ)
    (W : Set (AdelicGL2 (𝓞 F) F)) (hcov : CoversModCentre F W)
    (h0 : ∀ x ∈ W, φ x = 0) : φ = 0 := by
  funext g
  obtain ⟨γ, z, hmem⟩ := hcov g
  have h1 : φ (globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z) = 0 := h0 _ hmem
  have h2 : φ (centralScalar (𝓞 F) F z * (globalPoints (𝓞 F) F γ * g)) =
      ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (globalPoints (𝓞 F) F γ * g) :=
    hφ.central_transform ⟨z, Subgroup.mem_top z⟩ _
  rw [mul_centralScalar_comm, h2, hφ.left_invariant] at h1
  exact (mul_eq_zero.mp h1).resolve_left (Units.ne_zero _)
