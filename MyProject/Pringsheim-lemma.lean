import Mathlib

import Mathlib.Data.Complex.Basic

--yksi implementaatio:
variable {a : ℕ → ℝ }
def ha := a > 0

noncomputable def φ : ℂ  →  ℂ := fun l ↦ ∑' i, (l ^ i * a i)

--tömö mutta sitten pitää näyttää että fii on formalmultilinearseries
--radius of convergence (∈ (0, ))








--toinen implementaatio:

-- variable {φ : ℂ → ℂ } {hφ : (AnalyticAt ℂ φ 0)}
--     --{h_pos : ∀ n : ℕ , hφ.choose.coeff n = |(hφ.choose.coeff n).re|}
--     {h_real : ∀ n : ℕ , (hφ.choose.coeff n).im = 0}
--     {h_pos : ∀ n : ℕ , (hφ.choose.coeff n).re ≥ 0}
--     {h_rad_pos_fin : hφ.choose.radius.toReal > 0}
--     --{h_rad_fin : hφ.choose.radius < (infty : ENNReal) }
--     --{m : ℕ  }
-- noncomputable def ρ : ℝ  := hφ.choose.radius.toReal



theorem pringsheim (φ : ℂ → ℂ ) (hφ : AnalyticAt ℂ φ 0)
    (h_real : ∀ n : ℕ , (hφ.choose.coeff n).im = 0)
    (h_pos : ∀ n : ℕ , (hφ.choose.coeff n).re ≥ 0)
    (h_rad_pos_fin : hφ.choose.radius.toReal > 0)
    : ¬(AnalyticAt ℂ φ (Complex.ofReal hφ.choose.radius.toReal)) := by
    let ρ : ℝ  := hφ.choose.radius.toReal
    sorry






--def h_pos := hφ.choose

--power series muoto (from anaytic?)

--radius of convergence

--nonneg real coeff

















--kolmas implementaatio:
variable {a : FormalMultilinearSeries ℝ ℂ  ℂ } --{a_pos : ∀n : ℕ , a n 1 ≥ 0} --TODO: miten joukot menee
--noncomputable def rho := a.radius



--#check

example : 1 + 1 = 2 := by
    --hφ.choose.
    let moi := hφ.choose
    let moi2 := moi.coeff
    let h : ∀ n : ℕ , moi2 n ∈ reals = sorry
    --unfold FormalMultilinearSeries at a
    -- let moi := a 0
    -- unfold ContinuousMultilinearMap at a
    sorry

variable {m : ℝ }

--

--#check R

--#check Summable a

--def φ : ℂ → ℂ := ∑


--miten nimeän φ:lle radius of convergencen?

--

--analyyttinen ↔ potenssisarjamääritelmä suppenee
