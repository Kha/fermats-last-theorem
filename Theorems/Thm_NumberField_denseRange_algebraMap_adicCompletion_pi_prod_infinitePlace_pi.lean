import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi

set_option autoImplicit false
theorem NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi {K : Type*} [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    DenseRange (fun x : K =>
      ((fun v : S => algebraMap K (v.1.adicCompletion K) x),
       (fun w : NumberField.InfinitePlace K => algebraMap K w.Completion x))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi.solution
