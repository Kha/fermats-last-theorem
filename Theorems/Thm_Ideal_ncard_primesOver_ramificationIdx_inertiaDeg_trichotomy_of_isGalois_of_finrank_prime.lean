import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime

set_option autoImplicit false

open NumberField

theorem Ideal.ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (hℓ : (Module.finrank K L).Prime)
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver p] :
    ((p.primesOver (𝓞 L)).ncard = Module.finrank K L ∧
        p.ramificationIdx' P = 1 ∧ p.inertiaDeg' P = 1) ∨
      ((p.primesOver (𝓞 L)).ncard = 1 ∧
        p.ramificationIdx' P = Module.finrank K L ∧ p.inertiaDeg' P = 1) ∨
      ((p.primesOver (𝓞 L)).ncard = 1 ∧
        p.ramificationIdx' P = 1 ∧ p.inertiaDeg' P = Module.finrank K L) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime.solution
