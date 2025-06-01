

import Mathlib



lemma obvious' (φ : ℂ → ℂ ) (hφ : AnalyticAt ℂ φ 0)
  (h_neg : AnalyticAt ℂ φ (Complex.ofReal hφ.choose.radius.toReal))
  : ∃ser : FormalMultilinearSeries ℂ ℂ ℂ, ∃ε : ENNReal ,
    ε ≤ hφ.choose.radius ∧       --tätä ei periaatteessa tarvita, mutta tällä hetkellä tuntuu, että se ehkä helpottaa asioita.
    HasFPowerSeriesOnBall φ ser ↑hφ.choose.radius.toReal ε:= by
  let ρ  := hφ.choose.radius
  unfold AnalyticAt at h_neg
  cases' h_neg with ser_at_ρ h_ser_at_ρ
  unfold HasFPowerSeriesAt at h_ser_at_ρ
  cases' h_ser_at_ρ with ε' h_series
  have ε_pos : ε' > 0 := by exact h_series.r_pos
  have main : HasFPowerSeriesOnBall φ ser_at_ρ ↑ρ.toReal (min ε' ρ) :=
    {
      r_le := le_trans (min_le_left ε' ρ) h_series.r_le,
      r_pos := by
        simp only [lt_inf_iff, ENNReal.coe_pos]-- only [lt_inf_iff, ENNReal.coe_pos, Real.toNNReal_pos]
        exact ⟨ε_pos, hφ.choose_spec.radius_pos⟩,
      hasSum := by
        intro y hy
        have biggerBall : y ∈ EMetric.ball 0 ε' := by
          exact EMetric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_left ε' ρ))
        apply h_series.hasSum at biggerBall
        exact biggerBall
    }
  use ser_at_ρ
  use (min ε' ρ)
  exact ⟨by
    simp only [inf_le_iff]
    right
    exact Preorder.le_refl ρ
    , main⟩


example (f: ℕ → ℂ ) (t := Finset.range 1) :
  ∑' x , f x = f 0:= by sorry

example (f : ℕ → ℕ → ℂ ) (m : ℕ ) :
  --∑ n ∈ (Finset.range m), ∑ k ∈ (Finset.range n), f k
  (Finset.range m).sum (λ i => (Finset.range (i + 1) ).sum (λ j => f i j))
  = (Finset.range m).sum (λ j => (Finset.Ico j m ).sum (λ j => f i j)) := by
  --rw [Finset.sum_comm]
-- Now we are summing over j ∈ range m, i ∈ Icc j (m - 1)
-- because originally j ≤ i < m, so i ∈ [j, m)
  --rfl
  sorry
    -- simp only [Finset.range, Finset.sum_insert, Finset.not_mem_range_self] -- i = 0, 1, 2

    -- simp only [Multiset.range_succ, Multiset.range_zero, Multiset.cons_zero, Finset.mk_cons,
    --   Finset.cons_eq_insert, Finset.sum_mk, Finset.mem_insert, OfNat.ofNat_ne_one, Finset.mem_mk,
    --   Multiset.mem_singleton, OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert,
    --   Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton,
    --   one_ne_zero, Multiset.map_zero, Multiset.sum_zero, add_zero]-- only [Finset.range_zero, Finset.sum_empty]  -- i = 0 \u2192 sum is 0
    -- ring



open Finset BigOperators

def I : Finset ℕ := {0, 1, 2}

def J (i : ℕ) : Finset ℕ := {0, 1, 2}

def f (i j : ℕ) : ℕ := i + j

def result : ℕ := I.sum (λ i => (J i).sum (λ j => f i j))

#eval result  -- Output: 27



lemma sumform (z : ℂ  ) {φ :  ℂ → ℂ }
  {μ : ℝ }
  {ser_at_ρ : FormalMultilinearSeries ℂ ℂ ℂ }
  {ε : ENNReal}
  (has_ser_on_ball : HasFPowerSeriesOnBall φ ser_at_ρ ↑μ (2 / 3 * ε))
  : (↑z : ℂ) ∈ EMetric.ball 0 (2/3 * ε ) →    φ (↑μ + ↑z) = (∑' (b : ℕ), ((1 : ℝ)  / ↑(b.factorial)) • (iteratedFDeriv ℂ b φ ↑μ) fun _ ↦ ↑z)  := by--2 := by--∑' n, (fun n ↦ ((1 : ℝ)  / ↑(n.factorial)) • (iteratedFDeriv ℂ n φ ↑μ)) := by
  intro hz
  apply has_ser_on_ball.hasSum_iteratedFDeriv at hz
  apply HasSum.tsum_eq at hz
  simp only [hz.symm, smul_eq_mul, one_div, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast]          --tää on sus koska riippuu siitä, miten nimesin b:n


example (l μ : ℝ ) : ‖l + μ‖ₑ ≤ ‖l‖ₑ + ‖μ‖ₑ := by
  exact ENormedAddMonoid.enorm_add_le l μ

lemma dist_tri (l μ ρ : ℝ ) : ‖l - μ‖ₑ ≤ ‖l-ρ‖ₑ + ‖ρ-μ‖ₑ := by
  rw [(by simp only [sub_add_sub_cancel] : l - μ = (l - ρ) + (ρ - μ))]
  exact ENormedAddMonoid.enorm_add_le (l - ρ) (ρ - μ)



example  (b : ℕ) : Set.Finite {x | ∃ i ≤ b, x = (i, b)} := by
  -- The set is a subset of (ℕ × ℕ)
  -- It's equal to the image of {0, ..., b} under the map i ↦ (i, b)
  let s := (Finset.range (b + 1)).image (fun i ↦ (i, b))
  apply Set.Finite.ofFinset s
  intro x
  simp only [Set.mem_setOf_eq]-- only [Finset.mem_image, Finset.mem_range, mem_set_of_eq]
  constructor
  · intro hx
    use x.1
    constructor
    · sorry
    · sorry
    --rintro ⟨i, hi, rfl⟩
    --exact ⟨i, Nat.lt_succ_iff.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    sorry
    --exact ⟨i, Nat.lt_succ_iff.mpr hi, rfl⟩

open Function Set
--we need a lemma stating that f.uncurry is summble whenn f is twice summable
lemma switch_order (f : ℕ → ℕ → ℂ ) (hf : Summable (Function.uncurry fun j i ↦ {x | ∃ i ≤ j, (i, j) = x}.indicator (Function.uncurry f) (i, j)))
  : ∑' (i : ℕ ) (j: ℕ ), {(i, j) | i ≤ j }.indicator (f.uncurry) (i , j) = ∑' (j : ℕ) (i : ℕ ), {(i, j) | i ≤ j }.indicator (f.uncurry) (i , j):= by
  refine Summable.tsum_comm' ?_ ?_ ?_
  · exact hf
  · intro b
    have fin : Set.Finite {x | ∃ i ≤ b, (i, b) = x} := by
      sorry
    unfold Summable
    --use Finset.sum {x | ∃ i ≤ b, (i, b) = x} (Function.uncurry f)
    --clearly this is true but slightly painful
    sorry
  · intro c
    have right? : (Function.uncurry fun j i ↦ {x | ∃ i ≤ j, (i, j) = x}.indicator (Function.uncurry f) (i, j)) =  { (i, j)  : (ℕ × ℕ ) |  i ≤ j}.indicator (Function.uncurry f) := by
      ext x
      simp only [indicator, mem_setOf_eq, Prod.mk.injEq, and_true, exists_eq_right, uncurry]
      cases x with
      | mk i j =>


      · simp!
        sorry
      · sorry

    sorry

lemma exp_form (n : ℕ) (f :  ℂ [×n]→L[ℂ ] ℂ )--ContinuousMultilinearMap ℂ (fun i ↦ ℂ) ℂ)
  (l : ℂ ) :
  f (fun x ↦ l) = f (fun x ↦ 1)  * l^n  := by
  · let c' := f (fun x ↦ 1)
    let c : Fin n → ℂ := fun x ↦ l
    -- have difficult_form (m : (i : Fin n) → ℂ ) (s : Finset (Fin n))
    -- : (f fun (i : (Fin n)) => c i • m i) = (∏ i : (Fin n), c i) • f m := by
    --     exact ContinuousMultilinearMap.map_smul_univ f c m
    let m : Fin n → ℂ := fun x ↦ 1
    have slighty_easier_form
    : (f fun (i : (Fin n)) => c i • m i) = (∏ i : (Fin n), c i) • f m := by
      exact ContinuousMultilinearMap.map_smul_univ f c m
    simp only [smul_eq_mul] at *
    unfold m at slighty_easier_form
    unfold c at slighty_easier_form
    simp at *
    rewrite [slighty_easier_form]
    exact CommMonoid.mul_comm (l ^ n) (f fun x ↦ 1)


open scoped BigOperators
open Complex


--does it really need to be:
lemma nth_deriv_of_series_hard(r: ENNReal)  (hr: r > 0) (φ : ℂ → ℂ ) (b: ℕ ) (a : ℝ  ) --(hφ : AnalyticAt ℂ φ 0)
  (ser_at_0 : FormalMultilinearSeries ℂ ℂ ℂ )
  (on_ball_at_0  : HasFPowerSeriesOnBall φ ser_at_0 0 r)
  (ha : (↑a : ℂ ) ∈ EMetric.ball 0 r) --perkele, tää pitää ehkä muuttaa kuitenkin abstraktimmaksi
  : (iteratedFDeriv ℂ b φ) = fun a ↦ (fun (v : Fin n → ℂ )  ↦ (∑' m, a ^m * ser_at_0.coeff (m + b) * ((m + b).factorial/m.factorial)) * ∏(i : 𝔽in n), v i ):= by
  sorry


lemma change_fun_alku (f g : ℂ → ℂ ) (s : Set ℂ ) (h : EqOn f g s) --(x : ℂ ) (hx : x ∈ s) --saattaa olla turha
: EqOn (derivWithin f s) (derivWithin g s) s := by
  unfold EqOn
  intro a ha
  have heq : f a = g a := by exact h ha
  rw [derivWithin_congr h heq]

lemma chagne_fun_loppu (a : ℂ ) (f g : ℂ → ℂ ) (s : Set ℂ ) (h : EqOn f g s) (heq : EqOn (derivWithin f s) (derivWithin g s) s) (ha : a ∈ s)
: derivWithin f s a = derivWithin g s a := by
  refine derivWithin_congr h ?_
  exact h ha

lemma simplifying_of_der  (r : ENNReal) (m b' : ℕ ) (ser_at_0 : FormalMultilinearSeries ℂ ℂ ℂ )
: derivWithin (fun a ↦ ∑' (m : ℕ), a ^ m * ser_at_0.coeff (m + b') * (↑(m + b').factorial / ↑m.factorial))
    (EMetric.ball 0 r) a =
  ∑' (m : ℕ), a ^ m * ser_at_0.coeff (m + (b' + 1)) * ((↑m + ↑b' + 1) * ↑(m + b').factorial / ↑m.factorial)
  := by
  apply?
  sorry


lemma nth_deriv_of_series_valivaihe(r: ENNReal)  (hr: r > 0) (φ : ℂ → ℂ ) (b: ℕ ) --(a : ℝ  ) --(hφ : AnalyticAt ℂ φ 0)
  (ser_at_0 : FormalMultilinearSeries ℂ ℂ ℂ )
  (on_ball_at_0  : HasFPowerSeriesOnBall φ ser_at_0 0 r)
 -- (ha : (↑a : ℂ ) ∈ EMetric.ball 0 r) --perkele, tää pitää ehkä muuttaa kuitenkin abstraktimmaksi
  :EqOn (iteratedDerivWithin b φ (EMetric.ball 0 r)) ( fun a ↦ (∑' m, a ^m * ser_at_0.coeff (m + b) * ((m + b).factorial/m.factorial)) )  (EMetric.ball 0 r):= by
  --unfold EqOn
  induction b with | zero => _ | succ b' hb' => _
  · intro a ha
    simp only [iteratedDerivWithin_zero, add_zero]-- only [iteratedDeriv_zero, add_zero]

    --have obv : (a : ℂ ) ∈ EMetric.ball 0 r := by sorry
    apply on_ball_at_0.hasSum at ha
    have now : (∑' n, (ser_at_0 n) fun x ↦ a )= (φ (0 + a)) := by
      exact HasSum.tsum_eq ha
    simp at now
    rw [<- now]
    have eq_one (n: ℕ): ((↑n.factorial : ℂ ) / (↑n.factorial: ℂ )) = 1 := by
      refine (div_eq_one_iff_eq ?_).mpr rfl
      rewrite [Nat.cast_ne_zero]
      exact Nat.factorial_ne_zero n
    conv in (↑n.factorial / ↑n.factoriaPasswordl) =>
      rw [eq_one m]
    simp only [mul_one]
  · intro a ha
    #check iteratedDerivWithin
    rw [ iteratedDerivWithin_succ]
    have pikkuapu := chagne_fun_loppu
      a
      (iteratedDerivWithin b' φ (EMetric.ball 0 r))
      (fun a ↦ ∑' (m : ℕ), a ^ m * ser_at_0.coeff (m + b') * (↑(m + b').factorial / ↑m.factorial))
      (EMetric.ball 0 r)
      hb'
      (by sorry )
      ha
    rw [pikkuapu]
    clear pikkuapu
    simp!
    --specialize hb' ha

    sorry
  --refine iteratedFDeriv_tsum_apply ?_ ?_ ?_ ?_ ?_

  sorry

  lemma into_within (s: Set ℂ ) (s_open : IsOpen s) (b : ℕ ) (φ : ℂ → ℂ )
  : ∀ a' ∈ s, iteratedDeriv b φ a' = iteratedDerivWithin b φ s a':= by
    rw [iteratedDeriv_eq_iterate]
    induction b with | zero => _ | succ b' hb' => _
    · simp only [iterate_zero, id_eq, iteratedDerivWithin_zero, implies_true]
    · rw [iterate_succ']-- only [iterate_succ, comp_apply]
      simp only [comp_apply]
      intro a' ha'
      rw [ iteratedDerivWithin_succ]
      rw [<- derivWithin_of_isOpen s_open ha']
      apply derivWithin_congr
      · exact hb'
      · apply hb'
        exact ha'


--unsure if this is doable ;_;
lemma nth_deriv_of_series(r: ENNReal)  (hr: r > 0) (φ : ℂ → ℂ ) (b: ℕ ) (a : ℝ  ) --(hφ : AnalyticAt ℂ φ 0)
  (ser_at_0 : FormalMultilinearSeries ℂ ℂ ℂ )
  (on_ball_at_0  : HasFPowerSeriesOnBall φ ser_at_0 0 r) (s: Set ℂ ) (s_open : IsOpen s) (has : ↑a ∈ s)
  (ha : (↑a : ℂ ) ∈ EMetric.ball 0 r) --perkele, tää pitää ehkä muuttaa kuitenkin abstraktimmaksi
  : (iteratedFDeriv ℂ b φ a) (fun x ↦ l)= (∑' m, a ^m * ser_at_0.coeff (m + b) * ((m + b).factorial/m.factorial)) * l ^ b := by
  -- induction b with | zero => _ | succ b' hb' => _
  -- · simp only [iteratedFDeriv_zero_apply, add_zero]
  --   have obv : (a : ℂ ) ∈ EMetric.ball 0 r := by sorry
  --   sorry
  --   -- apply on_ball_at_a.hasSum at obv
  --   -- have now : (∑' n, (ser_at_0 n) fun x ↦ a )= (φ (0 + a)) := by
  --   --   exact HasSum.tsum_eq obv
  --   -- simp at now
  --   -- rw [<- now]
  --   -- have eq_one (n: ℕ): ((↑n.factorial : ℂ ) / (↑n.factorial: ℂ )) = 1 := by
  --   --   refine (div_eq_one_iff_eq ?_).mpr rfl
  --   --   rewrite [Nat.cast_ne_zero]
  --   --   exact Nat.factorial_ne_zero n
  --   -- conv in (↑n.factorial / ↑n.factoriaPasswordl) =>
  --   --   rw [eq_one m]
  --   -- simp only [mul_one

  -- · rewrite [iteratedFDeriv_succ_apply_left]
  --   #check (fderiv ℂ (iteratedFDeriv ℂ b' φ) a) l
  --   --levita iteratedfderiv
  --   --apply ass
  --   --pitäis toimia
   -- sorry
  rw [exp_form b (iteratedFDeriv ℂ b φ a) l]
  rw [<- iteratedDeriv_eq_iteratedFDeriv]
  have ball_open : IsOpen (EMetric.ball (0 : ℂ) r) := by exact EMetric.isOpen_ball
  have within := into_within (EMetric.ball 0 r) ball_open b φ a ha
  rewrite [within]
  simp only [mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq]
  left



  apply?
  sorry
  simp only [mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq]
  left
  induction b with | zero => _ | succ b' hb' => _
  · simp
    -- simp only [iteratedFDeriv_zero_apply, add_zero]
    have obv : (a : ℂ ) ∈ EMetric.ball 0 r := by sorry
    apply on_ball_at_0.hasSum at obv
    have now : (∑' n, (ser_at_0 n) fun x ↦ a )= (φ (0 + a)) := by
      exact HasSum.tsum_eq obv
    simp at now
    rw [<- now]
    have eq_one (n: ℕ): ((↑n.factorial : ℂ ) / (↑n.factorial: ℂ )) = 1 := by
      refine (div_eq_one_iff_eq ?_).mpr rfl
      rewrite [Nat.cast_ne_zero]
      exact Nat.factorial_ne_zero n
    conv in (↑n.factorial / ↑n.factoriaPasswordl) =>
      rw [eq_one m]
    simp only [mul_one]
  ·
    #check HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace on_ball_at_0

    simp!
    --rewrite [iteratedFDeriv]
    --rewrite [iteratedFDeriv_succ_apply_left]
    --simp only [fderiv_eq_smul_deriv, one_smul]

    sorry
  -- induction b
  -- · simp only [iteratedFDeriv_zero_apply, add_zero]
  --   have obv : (a : ℂ ) ∈ EMetric.ball 0 r := by sorry
  --   apply on_ball_at_a.hasSum at obv
  --   have now : (∑' n, (ser_at_0 n) fun x ↦ a )= (φ (0 + a)) := by
  --     exact HasSum.tsum_eq obv
  --   simp at now
  --   rw [<- now]
  --   have eq_one (n: ℕ): ((↑n.factorial : ℂ ) / (↑n.factorial: ℂ )) = 1 := by
  --     refine (div_eq_one_iff_eq ?_).mpr rfl
  --     rewrite [Nat.cast_ne_zero]
  --     exact Nat.factorial_ne_zero n
  --   conv in (↑n.factorial / ↑n.factoriaPasswordl) =>
  --     rw [eq_one m]
  --   simp only [mul_one]
  -- · --levita iteratedfderiv
  --   --apply ass
  --   --pitäis toimia
  --   sorry








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
  have usein := le_trans (min_le_left ε' ↑ρ.toNNReal) h_series.r_le
  have ε'_pos : ε' > 0 := by exact h_series.r_pos
  have obvious : HasFPowerSeriesOnBall φ ser_at_ρ ↑ρ (min ε' ρ.toNNReal) :=
    {
      r_le := usein,
      r_pos := by
        simp only [lt_inf_iff, ENNReal.coe_pos, Real.toNNReal_pos]
        exact ⟨ε'_pos, h_rad_pos_fin⟩,
      hasSum := by
        intro y hy
        have biggerBall : y ∈ EMetric.ball 0 ε' := by
          exact EMetric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_left ε' ↑ρ.toNNReal))
        apply h_series.hasSum at biggerBall
        exact biggerBall
    }
  let ε := (min ε' ρ.toNNReal)
  have ε_pos : 0 < ε.toReal := by sorry   --we know this is true
  let μ := ρ - (ε.toReal / 3)
  have has_pow_at_μ : HasFPowerSeriesOnBall φ ser_at_ρ ↑μ (2 / 3 * ε) := by
    exact {
      r_le := by
        have first : 2 / 3  * ε ≤ ε := by sorry  --THIS SHOULD BE TRIVIAL
        exact le_trans first usein
      r_pos := by
        norm_num
        exact obvious.r_pos
      hasSum := by
        have reformulation : ∀ y : ℂ, y ∈ EMetric.ball 0 (min ε' ↑ρ.toNNReal) →
          HasSum (fun n ↦ (ser_at_ρ n) fun x ↦ y) (φ (↑ρ + y))  := by
          intro y hy
          exact obvious.hasSum hy
        intro y hy
        sorry
    }

  let l : ℝ := ρ + ε.toReal / 4
  let l' := l - μ
  have l_le_bord : l < ρ + ε.toReal / 3 := by
    refine (Real.add_lt_add_iff_left ρ).mpr (div_lt_div_of_pos_left ε_pos ?_ ?_  )
    repeat norm_num
  have l'_in_bμ : (l' : ℂ) ∈ EMetric.ball 0 (2 / 3 * ε) := by
    simp only [EMetric.mem_ball, edist_zero_right]
    unfold l'
    have simplification : ‖l - μ‖ₑ.toReal = |l - μ| := by rfl
    have ε_ne_zero : ε.toReal ≠ 0 :=  Ne.symm (ne_of_lt ε_pos) --turha
    have ε_ne_top : ε ≠ ⊤ := by
      exact Ne.symm (ne_of_apply_ne ENNReal.toReal fun a ↦ ε_ne_zero (id (Eq.symm a))) --ENNReal.toReal_ne_zero
    have not_top : ‖l - μ‖ₑ ≠ ⊤ := by exact enorm_ne_top
    sorry

  have sum_at_l := sumform l' has_pow_at_μ l'_in_bμ
  let α := μ / ρ
  have α_lt_1 : α < 1 := by sorry
  let δ := (ρ - ε.toReal/3) / μ  - 1
  have δ_pos : δ > 0 := by sorry
  clear usein
  clear obvious
  clear l_le_bord
  clear l'_in_bμ
  --uusin pohdinta: missä on potenssihomma? (= mikä on iteratedFDeriv)
  have derivaattamuokkaus (n: ℕ):= nth_deriv_of_series
    (ENNReal.ofReal ρ)
    (by exact ENNReal.ofReal_pos.mpr h_rad_pos_fin)
    (φ)
    (n)
    (μ)
    (hφ.choose)
    (by sorry)  --simlpe
    (by sorry)  --simple



    --have final_sum : summable?∑' sorry := by sorry


  have analytic_at_too_far : AnalyticAt ℂ φ ↑(ρ + ε.toReal/4) := by sorry
  have size_ρplus : (↑|ρ  + ε.toReal/4| : ℂ ) = ρ + ε.toReal/4 := by sorry
  --formal_multilinear_series.not_summable_norm_of_radius_lt_nnnorm
  --exact?
  sorry


  lemma sarjayritys : 1 = 1 := by sorry



    theorem katko
        (φ : ℂ → ℂ)
        (hφ : AnalyticAt ℂ φ 0)
        (h_real : ∀ (n : ℕ), ((Exists.choose hφ).coeff n).im = 0)
        (h_pos : ∀ (n : ℕ), ((Exists.choose hφ).coeff n).re ≥ 0)
        (h_rad_pos_fin : (Exists.choose hφ).radius.toReal > 0)
        (ρ : ℝ := (Exists.choose hφ).radius.toReal)
        (ser_at_ρ : FormalMultilinearSeries ℂ ℂ ℂ)
        (ε' : ENNReal)
        (h_series : HasFPowerSeriesOnBall φ ser_at_ρ (↑(Exists.choose hφ).radius.toReal) ε')
        (usein : min ε' ↑ρ.toNNReal ≤ ser_at_ρ.radius)
        (ε'_pos : ε' > 0)
        (obvious : HasFPowerSeriesOnBall φ ser_at_ρ (↑ρ) (min ε' ↑ρ.toNNReal))
        (ε : ENNReal := min ε' ↑ρ.toNNReal)
        (ε_pos : 0 < ε.toReal)
        (μ : ℝ := ρ - ε.toReal / 3)
        (has_pow_at_μ : HasFPowerSeriesOnBall φ ser_at_ρ (↑μ) (2 / 3 * ε))
        (l : ℝ := ρ + ε.toReal / 4)
        (l' : ℝ := l - μ)
        (l_le_bord : l < ρ + ε.toReal / 3)
        (l'_in_bμ : ↑l' ∈ EMetric.ball 0 (2 / 3 * ε))
        (sum_at_l : φ (↑μ + ↑l') = ∑' (b : ℕ), (1 / ↑b.factorial) • (iteratedFDeriv ℂ b φ ↑μ) fun x ↦ ↑l')
        : False := by
        let α := μ / ρ

        sorry
