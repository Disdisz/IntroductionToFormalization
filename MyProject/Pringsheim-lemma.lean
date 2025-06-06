
import Mathlib



--I originally generated this lemma using chatgpt and then (heavily) modifiedi
lemma sum_switch_sigma (f: (b: ℕ ) × Set.Icc 0 b → ℂ ) (g : (k : ℕ ) × Set.Ici k → ℂ )
  (hf: Summable f) (hg: Summable g)
  (f_eq_g : ∀ (p : (b: ℕ ) × Set.Icc 0 b  ) (p2 : (k : ℕ ) × Set.Ici k ), p.1 = ↑p2.2 ∧ ↑p.2 = p2.1 → f p = g p2 ):
  ∑' (b : ℕ ) (k : Set.Icc 0 b), f ⟨b ,  k⟩ = ∑' (k : ℕ) (b : Set.Ici k), g ⟨k, b⟩ := by
  rewrite [<- Summable.tsum_sigma hf, <- Summable.tsum_sigma hg]
  let equ : (Σ b, Set.Icc 0 b) ≃ (Σ k, Set.Ici k) :=
    { toFun := λ ⟨b, y⟩ => ⟨↑y, ⟨ b, Set.mem_setOf.mpr y.property.2⟩ ⟩
      invFun := λ ⟨k, x⟩ => ⟨↑x, ⟨k, ⟨ by simp only [zero_le], Set.mem_setOf.mpr x.property⟩ ⟩⟩
      left_inv := by
        rintro ⟨b, y⟩
        simp only
      right_inv := by
        rintro ⟨k, x⟩
        simp only
    }
  have equ' : Function.support f ≃ Function.support g := by sorry   --less strict formulations for equ
  have f_eq_g' :  ∀ (x : ↑(Function.support f)), g ↑(equ' x) = f ↑x := by sorry -- l. s. form. for f_eq_g
  exact @Equiv.tsum_eq_tsum_of_support ℂ ((b: ℕ ) × Set.Icc 0 b) ((k : ℕ ) × Set.Ici k) _ _ _ _ equ' f_eq_g'
--it should be semi simple to use this to do the switching of the sums




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




lemma exp_form (n : ℕ) (f :  ℂ [×n]→L[ℂ ] ℂ )
  (l : ℂ ) :
  f (fun _ ↦ l) = f (fun _ ↦ 1)  * l^n  := by
  · let c' := f (fun x ↦ 1)
    let c : Fin n → ℂ := fun x ↦ l
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



lemma chagne_fun_loppu (a : ℂ ) (f g : ℂ → ℂ ) (s : Set ℂ ) (h : Set.EqOn f g s)  (ha : a ∈ s)--(heq : EqOn (derivWithin f s) (derivWithin g s) s) (ha : a ∈ s)
: derivWithin f s a = derivWithin g s a := derivWithin_congr h (h ha)


--shoud be shortenable
lemma simplifying_of_deriv (a : ℂ ) (r : ENNReal) (b' : ℕ ) (ser_at_0 : FormalMultilinearSeries ℂ ℂ ℂ )
  (u : ℕ → ℝ )  (ha : a ∈ (EMetric.ball 0 r) )
  (hu : Summable u)
  (hg : ∀ (n : ℕ ), Differentiable ℂ (fun (a : ℂ) ↦ a ^ n * ser_at_0.coeff (n + b') * (↑(n + b').factorial / ↑n.factorial) ) )
  (hg' : ∀ (n : ℕ ) (y : ℂ), ‖deriv ( fun (a : ℂ) ↦ a ^ n * ser_at_0.coeff (n + b') * (↑(n + b').factorial / ↑n.factorial)) y‖ ≤ u n)
  ( hg0 : Summable fun (n : ℕ ) =>  a ^ n * ser_at_0.coeff (n + b') * (↑(n + b').factorial / ↑n.factorial))
: derivWithin (fun a ↦ ∑' (m : ℕ), a ^ m * ser_at_0.coeff (m + b') * (↑(m + b').factorial / ↑m.factorial))
    (EMetric.ball 0 r) a =
  ∑' (m : ℕ), a ^ m * ser_at_0.coeff (m + (b' + 1)) * ((↑m + ↑b' + 1) * ↑(m + b').factorial / ↑m.factorial)
  := by
  have ball_open : IsOpen (EMetric.ball (0 : ℂ) r) := by exact EMetric.isOpen_ball
  rewrite [derivWithin_of_isOpen ball_open ha, deriv_tsum_apply hu hg hg' hg0]
  simp only [deriv_mul_const_field', differentiableAt_id', DifferentiableAt.pow,
    differentiableAt_const, deriv_mul, deriv_pow'', deriv_id'', mul_one, deriv_const', mul_zero,
    add_zero]
  have  hf : Summable (fun n ↦ ↑n * a ^ (n - 1) * ser_at_0.coeff (n + b') * (↑(n + b').factorial / ↑n.factorial))
    := by sorry
  rewrite [Summable.tsum_eq_zero_add hf] --pitää edetä toisesta suunnasta sittenkin kun toinen on summable
  simp only [CharP.cast_eq_zero, zero_tsub, pow_zero, mul_one, zero_add, zero_mul,
    Nat.factorial_zero, Nat.cast_one, div_one, Nat.cast_add, add_tsub_cancel_right]
  apply tsum_congr
  intro n
  --simp!
  calc
    (↑n + 1) * a ^ n * ser_at_0.coeff (n + 1 + b') * (↑(n + 1 + b').factorial / ↑(n + 1).factorial) =
      a ^ n * ser_at_0.coeff (n + 1 + b') * (↑n + 1) *(↑(n + 1 + b').factorial / ↑(n + 1).factorial)
      := by ring
    a ^ n * ser_at_0.coeff (n + 1 + b') * (↑n + 1) *(↑(n + 1 + b').factorial / ↑(n + 1).factorial)
      =  a ^ n * ser_at_0.coeff (n + 1 + b') * ↑(n + 1 + b').factorial * (↑n + 1)  / ↑(n + 1).factorial
      := by ring
    a ^ n * ser_at_0.coeff (n + 1 + b') * ↑(n + 1 + b').factorial * (↑n + 1)  / ↑(n + 1).factorial
      = a ^ n * ser_at_0.coeff (n + 1 + b') * ↑(n + 1 + b').factorial / ↑n.factorial
      := by
        have lol (n: ℕ) : (n + 1) / (n + 1).factorial  = 1 / (↑n.factorial : ℂ ) := by
          simp! only []  --sus
          simp only [Nat.succ_eq_add_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          --should be trivial
          sorry
        --rw [(lol n)] -- shoul be trivial
        sorry

  sorry --this is also clearly true





lemma nth_deriv_of_series_valivaihe(r: ENNReal)  (hr: r > 0) (φ : ℂ → ℂ ) (b: ℕ ) --(a : ℝ  ) --(hφ : AnalyticAt ℂ φ 0)
  (ser_at_0 : FormalMultilinearSeries ℂ ℂ ℂ )
  (on_ball_at_0  : HasFPowerSeriesOnBall φ ser_at_0 0 r)
 -- (ha : (↑a : ℂ ) ∈ EMetric.ball 0 r) --perkele, tää pitää ehkä muuttaa kuitenkin abstraktimmaksi
  : Set.EqOn (iteratedDerivWithin b φ (EMetric.ball 0 r)) ( fun a ↦ (∑' m, a ^m * ser_at_0.coeff (m + b)
    * ((m + b).factorial/m.factorial)) )  (EMetric.ball 0 r):= by
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
      ha
    rw [pikkuapu]
    clear pikkuapu
    simp!
    rw [simplifying_of_deriv (a) (r) (b') ser_at_0 (_) ha _ _ _]
    · sorry
    · sorry
    · sorry   --this is where all the summability things are I should have been focusing on.
    · sorry
    · sorry



  lemma into_within (s: Set ℂ ) (s_open : IsOpen s) (b : ℕ ) (φ : ℂ → ℂ )
  : ∀ a' ∈ s, iteratedDeriv b φ a' = iteratedDerivWithin b φ s a':= by
    rw [iteratedDeriv_eq_iterate]
    induction b with | zero => _ | succ b' hb' => _
    · simp only [Function.iterate_zero, id_eq, iteratedDerivWithin_zero, implies_true]
    · simp only [Function.iterate_succ', Function.comp_apply]--rw [iterate_succ, comp_apply]-- only [iterate_succ, comp_apply]
      intro a' ha'
      rw [ iteratedDerivWithin_succ]
      rw [<- derivWithin_of_isOpen s_open ha']
      apply derivWithin_congr
      · exact hb'
      · apply hb'
        exact ha'



lemma nth_deriv_of_series' (l: ℂ )(r: ENNReal)  (hr: r > 0) (φ : ℂ → ℂ ) (b: ℕ ) (a : ℝ  ) --(hφ : AnalyticAt ℂ φ 0)
  (ser_at_0 : FormalMultilinearSeries ℂ ℂ ℂ )
  (on_ball_at_0  : HasFPowerSeriesOnBall φ ser_at_0 0 r) (s: Set ℂ ) (s_open : IsOpen s) (has : ↑a ∈ s)
  (ha : (↑a : ℂ ) ∈ EMetric.ball 0 r)
  : (iteratedFDeriv ℂ b φ a) (fun x ↦ l)= (∑' m, a ^m * ser_at_0.coeff (m + b) * ((m + b).factorial/m.factorial)) * l ^ b := by
  rw [exp_form b (iteratedFDeriv ℂ b φ a) l]
  rw [<- iteratedDeriv_eq_iteratedFDeriv]
  have ball_open : IsOpen (EMetric.ball (0 : ℂ) r) := by exact EMetric.isOpen_ball
  have within := into_within (EMetric.ball 0 r) ball_open b φ a ha
  rewrite [within]
  simp only [mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq]
  left

  --so here i was intenting to use the nth_deriv_of_series_valivaihe, but the eqOn
  --  instead of actual equality might also be a problem for the way this is factored.
  --  (for the underlying mathematics this is fine)

  sorry




lemma nth_deriv_of_series  (l: ℂ )(r: ENNReal)  (hr: r > 0) (φ : ℂ → ℂ ) (b: ℕ ) (a : ℝ  ) --(hφ : AnalyticAt ℂ φ 0)
  (ser_at_0 : FormalMultilinearSeries ℂ ℂ ℂ )
  (on_ball_at_0  : HasFPowerSeriesOnBall φ ser_at_0 0 r)
  (ha : (↑a : ℂ ) ∈ EMetric.ball 0 r)
  : (iteratedFDeriv ℂ b φ a) (fun x ↦ l)= (∑' m, a ^m * ser_at_0.coeff (m + b) * ((m + b).factorial/m.factorial)) * l ^ b := by
    have ball_open : IsOpen (EMetric.ball (0 : ℂ) r) := by exact EMetric.isOpen_ball
    exact nth_deriv_of_series' l r hr φ b a ser_at_0 on_ball_at_0 (EMetric.ball (0 : ℂ) r) ball_open ha ha





--this proof was somehow difficult to formulate into smaller pieces
theorem pringsheim (φ : ℂ → ℂ ) (hφ : AnalyticAt ℂ φ 0)
  (h_real : ∀ n : ℕ , (hφ.choose.coeff n).im = 0)
  (h_pos : ∀ n : ℕ , (hφ.choose.coeff n).re ≥ 0)
  (h_rad_pos_fin : hφ.choose.radius.toReal > 0)  --ehkä tämä toiseen muotoon (pos oletus pois tästä koska on jo analyticatissa)
  : ¬(AnalyticAt ℂ φ (Complex.ofReal hφ.choose.radius.toReal)) := by
  let ρ : ℝ  := hφ.choose.radius.toReal
  by_contra counter
  cases' counter with ser_at_ρ h_ser_at_ρ
  cases' h_ser_at_ρ with ε' h_ser_on_ball_ρ
  have usein := le_trans (min_le_left ε' ↑ρ.toNNReal) h_ser_on_ball_ρ.r_le
  have ε'_pos : ε' > 0 := h_ser_on_ball_ρ.r_pos
  have obvious : HasFPowerSeriesOnBall φ ser_at_ρ ↑ρ (min ε' ρ.toNNReal) :=  --tuo min siksi että on kätevää, ettei epsilon ole ääretön
    {
      r_le := usein,
      r_pos := by
        simp only [lt_inf_iff, ENNReal.coe_pos, Real.toNNReal_pos]
        exact ⟨ε'_pos, h_rad_pos_fin⟩,
      hasSum := by
        intro y hy
        have biggerBall : y ∈ EMetric.ball 0 ε' := by
          exact EMetric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_left ε' ↑ρ.toNNReal))
        apply h_ser_on_ball_ρ.hasSum at biggerBall
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
          intro y
          exact obvious.hasSum
        intro y hy
        sorry
    }
  clear usein
  let l : ℝ := ρ + ε.toReal / 4
  let l' := l - μ
  have l_le_bord : l < ρ + ε.toReal / 3 :=
    (Real.add_lt_add_iff_left ρ).mpr (div_lt_div_of_pos_left ε_pos (by norm_num) (by norm_num)  )
  have l'_in_bμ : (l' : ℂ) ∈ EMetric.ball 0 (2 / 3 * ε) := by
    simp only [EMetric.mem_ball, edist_zero_right]
    have simplification : ‖l - μ‖ₑ.toReal = |l - μ| := by rfl
    have ε_ne_zero : ε.toReal ≠ 0 :=  Ne.symm (ne_of_lt ε_pos)
    have ε_ne_top : ε ≠ ⊤ :=
      Ne.symm (ne_of_apply_ne ENNReal.toReal fun a ↦ ε_ne_zero (id (Eq.symm a)))
    have not_top : ‖l - μ‖ₑ ≠ ⊤ := enorm_ne_top
    sorry  --clearly true, coercion difficulties

  have sum_at_l := sumform l' has_pow_at_μ l'_in_bμ
  let α := μ / ρ
  have α_lt_1 : α < 1 := by sorry
  let δ := (ρ - ε.toReal/3) / μ  - 1
  have δ_pos : δ > 0 := by sorry
  clear obvious l_le_bord l'_in_bμ

  have sum_manipulated :
    (∑' (b : ℕ), (1 / (↑b.factorial : ℂ) ) • (∑' (m : ℕ), ↑μ ^ m * (Exists.choose hφ).coeff (m + b)
      * (↑(m + b).factorial / ↑m.factorial)) * ↑l' ^ b ) = φ (↑μ + ↑l') := by
    rewrite [sum_at_l]
    apply tsum_congr
    intro b
    rewrite [ nth_deriv_of_series ↑l' (ENNReal.ofReal ρ)
      (by exact ENNReal.ofReal_pos.mpr h_rad_pos_fin) (φ) (b) (μ) (hφ.choose)
      (by sorry)  --simple
      (by sorry)  --simple
      ]
    simp [one_div, mul_assoc, smul_eq_mul, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_natCast]
  simp only [one_div, smul_eq_mul, ← tsum_mul_left] at sum_manipulated--change φ (↑μ + ↑l') = (∑' (b : ℕ), (1 / ↑b.factorial) • (iteratedFDeriv ℂ b φ ↑μ) fun x ↦ ↑l') at sum_at_l
  have lb_in : ∀b: ℕ ,  (∑' (x : ℕ), (↑b.factorial)⁻¹ * (↑μ ^ x * (Exists.choose hφ).coeff (x + b) *
      (↑(x + b).factorial / ↑x.factorial))) * ↑l' ^ b
      = (∑' (x : ℕ), (↑b.factorial)⁻¹ * (↑μ ^ x * (Exists.choose hφ).coeff (x + b) *
      (↑(x + b).factorial / ↑x.factorial)) *  ↑l' ^ b)
       := by
        intro b
        rw [<- tsum_mul_right]
  simp only [lb_in] at sum_manipulated
  clear lb_in
  rewrite [Summable.tsum_comm (by sorry) ] at sum_manipulated    --summability
  have reorder: ∀ b c : ℕ,
    (↑c.factorial)⁻¹ * (↑μ ^ b * (Exists.choose hφ).coeff (b + c) * (↑(b + c).factorial / ↑b.factorial)) * ↑l' ^ c
    = ↑μ ^ b * (Exists.choose hφ).coeff (b + c) * (↑c.factorial)⁻¹ * (  (↑(b + c).factorial / ↑b.factorial)) * ↑l' ^ c
    := by
      intro _ _
      ring
  simp [reorder] at sum_manipulated
  clear reorder
  have into_choose_form : ∀ b c : ℕ,
    (↑c.factorial : ℂ )⁻¹ * (↑(b + c).factorial / ↑b.factorial)
    =  (↑(b + c).factorial / (↑c.factorial * ↑b.factorial)) := by
    intro _ _
    ring
  have out_of_sum : ∀ b : ℕ , ∑'  (c : ℕ) ,
    ↑μ ^ b * (Exists.choose hφ).coeff (b + c) * (↑c.factorial)⁻¹ * (↑(b + c).factorial / ↑b.factorial) * ↑l' ^ c =
    ↑μ ^ b * ∑'  (c : ℕ) ,
    (Exists.choose hφ).coeff (b + c) * (↑c.factorial)⁻¹ * (↑(b + c).factorial / ↑b.factorial) * ↑l' ^ c
    := by
    intro b
    sorry

  --Here ^^ I try to take some coefficients out of the sum, but the inner sum also needs some re-indexing.
  --After that, the inner sum would reduce to a constant, and that would reduce the entire sum essentially
  --  to the same form as the function in the goal in the end (ser n * ↑(ρ + ε.toReal / 4) ^ n, this is
  --  equal because these are all positive).
  --Then the only issue left is that this is inside the tsum and not inside a summable; I think this
  --  might be a big problem, but hepefullu the sum manipulations have been at least slightly usefull.




  have analytic_at_too_far : AnalyticAt ℂ φ ↑(ρ + ε.toReal/4) := by sorry
  have size_ρplus : (norm (↑(ρ  + ε.toReal/4) : ℂ) ) = ρ + ε.toReal/4 := by sorry
  have ge_rho : (norm (↑(ρ  + ε.toReal/4) : ℂ) ) > ρ := by
    rw [size_ρplus]
    linarith
  let ser := hφ.choose
  #check ser
  #check FormalMultilinearSeries.not_summable_norm_of_radius_lt_nnnorm
  apply FormalMultilinearSeries.not_summable_norm_of_radius_lt_nnnorm (x :=  (↑(ρ  + ε.toReal/4) : ℂ)) ser (by sorry)


  sorry
