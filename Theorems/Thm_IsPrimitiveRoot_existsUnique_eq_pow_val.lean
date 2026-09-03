import Mathlib
import P2M.Util
import P2M.Sol.S_IsPrimitiveRoot_existsUnique_eq_pow_val

set_option autoImplicit false
theorem IsPrimitiveRoot.existsUnique_eq_pow_val
    {R ι : Type*} [CommRing R] [IsDomain R] {ζ : Rˣ} {p : ℕ} [NeZero p] (hζ : IsPrimitiveRoot ζ p) (f : ι → Rˣ) (hf : ∀ i, f i ^ p = 1) :
    ∃! c : ι → ZMod p, ∀ i, f i = ζ ^ (c i).val := by p2m_exact_reverting @_root_.P2MW.S_IsPrimitiveRoot_existsUnique_eq_pow_val.solution
