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


--lemma obvious? : --(h : HasFPowerSeriesOnBall )
lemma obvious' (φ : ℂ → ℂ ) (hφ : AnalyticAt ℂ φ 0)
    (h_real : ∀ n : ℕ , (hφ.choose.coeff n).im = 0)
    (h_pos : ∀ n : ℕ , (hφ.choose.coeff n).re ≥ 0)
    (h_rad_pos_fin : hφ.choose.radius ≠ infty)  --ehkä tämä toiseen muotoon (pos oletus pois tästä koska on jo analyticatissa)
    (h_neg : AnalyticAt ℂ φ (Complex.ofReal hφ.choose.radius.toReal))
    : ∃ser : FormalMultilinearSeries ℂ ℂ ℂ, ∃ε : ENNReal ,
        ε ≤ hφ.choose.radius ∧
        HasFPowerSeriesOnBall φ ser ↑hφ.choose.radius.toReal ε:= by
    -- let ρ  := hφ.choose.radius
    -- unfold AnalyticAt at h_neg
    -- cases' h_neg with ser_at_ρ h_ser_at_ρ
    -- unfold HasFPowerSeriesAt at h_ser_at_ρ
    -- cases' h_ser_at_ρ with ε' h_series
    -- unfold HasFPowerSeriesOnBall at h_series
    -- have ε_pos : ε' > 0 := by exact h_series.r_pos
    -- have obvious : HasFPowerSeriesOnBall φ ser_at_ρ ↑ρ.toReal (min ε' ρ) :=
    --     {
    --         r_le := le_trans (min_le_left ε' ρ) h_series.r_le,
    --         r_pos := by
    --             simp only [lt_inf_iff, ENNReal.coe_pos]-- only [lt_inf_iff, ENNReal.coe_pos, Real.toNNReal_pos]
    --             exact ⟨ε_pos, by h_neg.choose_spec.choose_spec⟩,
    --         hasSum := by
    --             intro y hy
    --             have biggerBall : y ∈ EMetric.ball 0 ε' := by
    --                 exact EMetric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_left ε' ↑ρ.toNNReal))
    --             apply h_series.hasSum at biggerBall
    --             exact biggerBall
    --     }
    -- use ser_at_ρ
    -- use (min ε' ρ.toNNReal)
    -- exact ⟨by
    --     simp only [inf_le_iff]
    --     right

    --     sorry
    --     , obvious⟩
    sorry



--hada martin
theorem pringsheim (φ : ℂ → ℂ ) (hφ : AnalyticAt ℂ φ 0)
    (h_real : ∀ n : ℕ , (hφ.choose.coeff n).im = 0)
    (h_pos : ∀ n : ℕ , (hφ.choose.coeff n).re ≥ 0)
    (h_rad_pos_fin : hφ.choose.radius.toReal > 0)  --ehkä tämä toiseen muotoon (pos oletus pois tästä koska on jo analyticatissa)
    : ¬(AnalyticAt ℂ φ (Complex.ofReal hφ.choose.radius.toReal)) := by
    let ρ : ℝ  := hφ.choose.radius.toReal
    by_contra hmoi
    unfold AnalyticAt at hmoi
    cases' hmoi with ser_at_ρ h_ser_at_ρ
    unfold HasFPowerSeriesAt at h_ser_at_ρ
    cases' h_ser_at_ρ with ε' h_series
    unfold HasFPowerSeriesOnBall at h_series
    have ε_pos : ε' > 0 := by exact h_series.r_pos
    have obvious : HasFPowerSeriesOnBall φ ser_at_ρ ↑ρ (min ε' ρ.toNNReal) :=
        {
            r_le := le_trans (min_le_left ε' ↑ρ.toNNReal) h_series.r_le,
            r_pos := by
                simp only [lt_inf_iff, ENNReal.coe_pos, Real.toNNReal_pos]
                exact ⟨ε_pos, h_rad_pos_fin⟩,
            hasSum := by
                intro y hy
                have biggerBall : y ∈ EMetric.ball 0 ε' := by
                    exact EMetric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_left ε' ↑ρ.toNNReal))
                apply h_series.hasSum at biggerBall
                exact biggerBall
        }
    let ε := (min ε' ρ.toNNReal)
    let μ := ρ - ε.toReal



    --have ε_fin : ε < hφ.choose.radius := by exact h_series.r_le

    --rename_bvar (Exists.choose hφ).radius.toReal ρ at *


    sorry

    --Complex.taylorSeries_eq_on_ball'








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
