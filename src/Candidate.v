Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z.


Module Type Cand.
  
  Parameter cand : Type.
  Parameter cand_all : list cand.
  Parameter cand_fin : forall c: cand, In c cand_all.
  Parameter dec_cand : forall n m : cand, {n = m} + {n <> m}.
  Parameter cand_not_nil : cand_all <> [].

End Cand.




  
