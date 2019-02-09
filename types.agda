{-# OPTIONS --without-K --safe #-}

data Ty : Set where
  o : Ty
  _⟶_ : Ty → Ty → Ty
  
data Con : Set where
  ● : Con
  _,_ : Con → Ty → Con
