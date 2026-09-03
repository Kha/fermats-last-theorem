import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_exists_pow_eq_iff_exists_rootOfUnity_coboundary

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.exists_pow_eq_iff_exists_rootOfUnity_coboundary
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} {a : Kˣ} {α : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    (∃ b : Kˣ, b ^ p = a) ↔
      ∃ ζ : Lˣ, ζ ^ p = 1 ∧ ∀ σ : L ≃ₐ[K] L, σ • ζ / ζ = kummerCocycle α σ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_exists_pow_eq_iff_exists_rootOfUnity_coboundary.solution
