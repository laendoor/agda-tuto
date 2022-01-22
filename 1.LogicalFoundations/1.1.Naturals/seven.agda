data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

one   = suc zero
two   = suc one
three = suc two
four  = suc three
five  = suc four
six   = suc five

seven : ℕ
seven = suc six

