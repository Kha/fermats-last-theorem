import Mathlib
import Definitions.Def_ModularCurve_HpoolLevelRing
import P2M.Util
import P2M.Sol.S_ModularCurve_HpoolLevelRing_exists_forall_etale_levelRing_of_etale_fiber

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open Polynomial ModularCurve ModularCurve.HpoolLevelRing
open scoped TensorProduct

theorem ModularCurve.HpoolLevelRing.exists_forall_etale_levelRing_of_etale_fiber
    (p : ℕ) [Fact p.Prime] [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) (u : Afin p) (g : ℤ[X])
    [Module.Finite (Localization.Away (p : ℤ)) (levelRing p p u g)]
    [Module.Flat (Localization.Away (p : ℤ)) (levelRing p p u g)]
    (hgen : ∀ (P : Ideal (Localization.Away (p : ℤ))) [P.IsPrime], P = ⊥ →
      Algebra.Etale P.ResidueField (P.Fiber (levelRing p p u g)))
    (hℓet : ∀ (P : Ideal (Localization.Away (p : ℤ))) [P.IsPrime],
      P = Ideal.span {algebraMap ℤ (Localization.Away (p : ℤ)) ℓ} →
      Algebra.Etale P.ResidueField (P.Fiber (levelRing p p u g))) :
    ∃ c : ℤ, c ≠ 0 ∧ ¬ (ℓ : ℤ) ∣ c ∧ (p : ℤ) ∣ c ∧
      ∀ f : ℤ, f ≠ 0 → c ∣ f → Algebra.Etale (Localization.Away f) (levelRing p f u g) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_levelRing_of_etale_fiber.solution
