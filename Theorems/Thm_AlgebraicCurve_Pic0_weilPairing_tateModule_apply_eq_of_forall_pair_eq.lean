import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_weilPairing_tateModule_apply_eq_of_forall_pair_eq

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.weilPairing_tateModule_apply_eq_of_forall_pair_eq
    (K F F' : Type) [Field K] [Field F] [Algebra K F] [Field F'] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (ℓ : ℕ) [Fact ℓ.Prime]
    (ζ : ℕ → K) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n))

    (e : TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : ∀ (n : ℕ) (W : DivisorialWeilPairingData K F (ℓ ^ n))
        (a b : TateModule ℓ (Pic0 K F)) (a' b' : Pic0.torsion K F (ℓ ^ n)),
        (a' : Pic0 K F) = (a : ℕ → Pic0 K F) n →
        (b' : Pic0 K F) = (b : ℕ → Pic0 K F) n →
        W.pair a' b' = ζ n ^ ((e a b).appr n))
    (e' : TateModule ℓ (Pic0 K F') →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F') →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he' : ∀ (n : ℕ) (W' : DivisorialWeilPairingData K F' (ℓ ^ n))
        (a b : TateModule ℓ (Pic0 K F')) (a' b' : Pic0.torsion K F' (ℓ ^ n)),
        (a' : Pic0 K F') = (a : ℕ → Pic0 K F') n →
        (b' : Pic0 K F') = (b : ℕ → Pic0 K F') n →
        W'.pair a' b' = ζ n ^ ((e' a b).appr n))

    (hW : ∀ n : ℕ, Nonempty (DivisorialWeilPairingData K F (ℓ ^ n)))
    (hW' : ∀ n : ℕ, Nonempty (DivisorialWeilPairingData K F' (ℓ ^ n)))

    (S : Pic0 K F →+ Pic0 K F') (T : Pic0 K F' →+ Pic0 K F)
    (hST : ∀ (n : ℕ) (W : DivisorialWeilPairingData K F (ℓ ^ n))
        (W' : DivisorialWeilPairingData K F' (ℓ ^ n))
        (x Ty : Pic0.torsion K F (ℓ ^ n)) (Sx y : Pic0.torsion K F' (ℓ ^ n)),
        (Sx : Pic0 K F') = S (x : Pic0 K F) →
        (Ty : Pic0 K F) = T (y : Pic0 K F') →
        W'.pair Sx y = W.pair x Ty)

    (CS : TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F'))
    (hCS : ∀ (a : TateModule ℓ (Pic0 K F)) (n : ℕ),
        ((CS a : TateModule ℓ (Pic0 K F')) : ℕ → Pic0 K F') n = S ((a : ℕ → Pic0 K F) n))
    (CT : TateModule ℓ (Pic0 K F') →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F))
    (hCT : ∀ (b : TateModule ℓ (Pic0 K F')) (n : ℕ),
        ((CT b : TateModule ℓ (Pic0 K F)) : ℕ → Pic0 K F) n = T ((b : ℕ → Pic0 K F') n))
    (a : TateModule ℓ (Pic0 K F)) (b : TateModule ℓ (Pic0 K F')) :
    e' (CS a) b = e a (CT b) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_weilPairing_tateModule_apply_eq_of_forall_pair_eq.solution
