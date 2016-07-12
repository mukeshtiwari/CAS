Section Untyped_CAS. 


Inductive uEQV : Type := 
   | ueqvBase    : te_base -> uEQV 
   | ueqvList    : uEQV -> uEQV
   | ueqvSet     : uEQV -> uEQV
   | ueqvProduct : uEQV → uEQV → uEQV 
   | ueqvSum     : uEQV → uEQV → uEQV 
   . 

Inductive SG :=
   | sAnd            : SG 
   | sOr             : SG 
   | sMin            : NumberType → SG
   | sMax            : NumberType → SG
   | sPlus           : NumberType → SG
   | sTimes          : NumberType → SG
   | sLeftSum        : SG → SG → SG
   | sRightSum       : SG → SG → SG
   | sProduct        : SG → SG → SG
   | sLeft           : uEQV → SG
   | sRight          : uEQV → SG
   | sConcat         : uEQV → SG
   | sUnion         : uEQV → SG
   .

Inductive TR :=
   | trFromSemigroup : SG → TR 
   | trLeftSum       : TR → TR → TR
   | trRightSum      : TR → TR → TR
   | trProduct       : TR → TR → TR
   . 

Inductive Error := 
   | mkError : string → Error 
   . 

Fixpoint eqv_infer (x : uEQV) : { s : te & tEQV s} + Error := 
   match x with 
   | ueqvBase    b   => inl _ (existT (λ s : te,  tEQV s) (te_from_base b) (eqvBase b))
   | ueqvList    x   => 
     match eqv_infer x with 
     | inr s => inr _ s  
     | inl (existT s s_exp) => 
         inl _ (existT (λ s : te, tEQV s) (te_list s) (eqvList s s_exp))         
     end 
   | ueqvSet    x   => 
     match eqv_infer x with 
     | inr s => inr _ s  
     | inl (existT s s_exp) => 
         inl _ (existT (λ s : te, tEQV s) (te_set s) (eqvSet s s_exp))         
     end 
   | ueqvProduct x y => 
     match eqv_infer x, eqv_infer y with 
     | inr s, _ => inr _ s  
     | _, inr s => inr _ s 
     | inl (existT s s_exp), inl (existT t t_exp) => 
         inl _ (existT (λ s : te, tEQV s)  (te_prod s t) (eqvProduct s t s_exp t_exp))
     end 
   | ueqvSum     x y => 
     match eqv_infer x, eqv_infer y with 
     | inr s, _ => inr _ s  
     | _, inr s => inr _ s 
     | inl (existT s s_exp), inl (existT t t_exp) => 
         inl _ (existT (λ s : te, tEQV s)  (te_sum s t) (eqvSum s t s_exp t_exp))
     end 
   end. 

Fixpoint sg_infer (x : SG) : { s : te & tSG s} + Error := 
   match x with 
   | sAnd           => inl _ (existT (λ s : te, tSG s) (te_from_base te_bool) stAnd)
   | sOr            => inl _ (existT (λ s : te, tSG s) (te_from_base te_bool) stOr)
   | sMin _         => inl _ (existT (λ s : te, tSG s) (te_from_base (te_num Nat)) (stMin Nat))
   | sMax _         => inl _ (existT (λ s : te, tSG s) (te_from_base (te_num Nat)) (stMax Nat))
   | sPlus _        => inl _ (existT (λ s : te, tSG s) (te_from_base (te_num Nat)) (stPlus Nat))
   | sTimes _       => inl _ (existT (λ s : te, tSG s) (te_from_base (te_num Nat)) (stTimes Nat))
   | sLeftSum l r   => 
     match sg_infer l, sg_infer r with 
     | inr s, _ => inr _ s  
     | _, inr s => inr _ s 
     | inl (existT s s_exp), inl (existT t t_exp) => 
         inl _ (existT (λ s : te, tSG s)  (te_sum s t) (stLeftSum s t s_exp t_exp))
     end 
   | sRightSum l r  => 
     match sg_infer l, sg_infer r with 
     | inr s, _ => inr _ s 
     | _, inr s => inr _ s 
     | inl (existT s s_exp), inl (existT t t_exp) => 
         inl _ (existT (λ s : te, tSG s)  (te_sum s t) (stRightSum s t s_exp t_exp))
     end 
   | sProduct  l r  => 
     match sg_infer l, sg_infer r with 
     | inr s, _ => inr _ s       
     | _, inr s => inr _ s 
     | inl (existT s s_exp), inl (existT t t_exp) => 
         inl _ (existT (λ s : te, tSG s)  (te_prod s t) (stProduct s t s_exp t_exp))
     end 
   | sLeft e  => 
     match eqv_infer e with 
     | inr s => inr _ s       
     | inl (existT s s_exp) => 
         inl _ (existT (λ s : te, tSG s)  s (stLeft s s_exp))
     end 
   | sRight e  => 
     match eqv_infer e with 
     | inr s => inr _ s       
     | inl (existT s s_exp) => 
         inl _ (existT (λ s : te, tSG s)  s (stRight s s_exp))
     end 
   | sConcat e  => 
     match eqv_infer e with 
     | inr s => inr _ s       
     | inl (existT s s_exp) => 
         inl _ (existT (λ s : te, tSG s)  (te_list s) (stConcat s s_exp))
     end 
   | sUnion e  => 
     match eqv_infer e with 
     | inr s => inr _ s       
     | inl (existT s s_exp) => 
         inl _ (existT (λ s : te, tSG s)  (te_set s) (stUnion s s_exp))
     end 
   end 
   .

Definition tr_coerce_left  : ∀ (s t u : te), (t = u) → tTR s t → tTR s u
:= λ s : te,  λ t : te,  λ u : te,  λ p : (t = u),  λ r : tTR s t,  
   match p with eq_refl => r end. 

Definition tr_coerce_right : ∀ (s t u : te), (s = u) → tTR s t → tTR u t
:= λ s : te,  λ t : te,  λ u : te,  λ p : (s = u),  λ r : tTR s t,  
   match p with eq_refl => r end. 

Fixpoint eq_te (x y : te) : bool :=
   match x, y with
   | te_from_base te_bool, te_from_base te_bool           => true 
   | te_from_base (te_num Nat), te_from_base (te_num Nat) => true 
   | te_list y, te_list v   =>  eq_te y v
   | te_sum x y, te_sum u v   => (eq_te x u) && (eq_te y v) 
   | te_prod x y, te_prod u v => (eq_te x u) && (eq_te y v) 
   | _, _                     => false 
   end.

Lemma product_lemma : ∀ (s t u v : te), eq_te (te_prod s u) (te_prod t v) = true → 
    (eq_te s t) = true /\  (eq_te u v) = true.  
Proof. 
    intros. simpl in H. 
    assert (Q :=  andb_true_implies (eq_te s t ) (eq_te u v )).
    apply (Q H).
Defined. 
     
Lemma sum_lemma : ∀ (s t u v : te), eq_te (te_sum s u) (te_sum t v) = true → 
    (eq_te s t) = true /\  (eq_te u v) = true.  
Proof. 
    intros. simpl in H. 
    assert (Q :=  andb_true_implies (eq_te s t ) (eq_te u v )).
    apply (Q H).
Defined. 
     

Lemma eq_te_complete : ∀ s t : te, (eq_te s t) = true → (s = t). 
Proof. 
   induction s; induction t; simpl. 
   induction t. destruct t. intro. reflexivity.  intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   destruct n. intro t. destruct t. 
      destruct t. intro. discriminate. 
      destruct n. intro. reflexivity.
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro H. rewrite (IHs t H). reflexivity. 
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro H. assert (Q := product_lemma _ _ _ _ H).  
    destruct Q as [H1 H2]. 
    rewrite (IHs1 _ H1). rewrite (IHs2 _ H2). reflexivity. 
   intro. discriminate. 
   intro. discriminate.     
   intro. discriminate. 
   intro. discriminate. 
   intro. discriminate. 
   intro H. assert (Q := sum_lemma _ _ _ _ H). 
    destruct Q as [H1 H2]. 
    rewrite (IHs1 _ H1). rewrite (IHs2 _ H2). reflexivity. 
Defined. 

Definition equal_te1 (s t : te) : option (eq_te s t = true) := equal_true (eq_te s t). 

Definition equal_te2 (s t : te) : option (s = t) := 
   match equal_te1 s t with 
   | None => None 
   | Some p => Some (eq_te_complete _ _ p) 
   end. 

Fixpoint tr_infer (x : TR) : { s : te & { t : te & tTR s t}} + Error := 
   match x with 
   | trFromSemigroup s_exp => 
     match (sg_infer s_exp) with 
     | inr s => inr _ s 
     | inl (existT s st_exp) => 
          inl _ (existT (λ s : te, { t : te & tTR s t}) s 
                   (existT (λ t, tTR s t) s (trtFromSemigroup s st_exp)))
     end 
   | trLeftSum  l r => 
     match (tr_infer l), (tr_infer r) with 
     | inr s, _ => inr _ s
     | _, inr s => inr _ s
     | inl (existT s (existT t1 t_l)), inl (existT u (existT t2 t_r)) => 
         match equal_te2 t2 t1 with 
         | None => inr _ (mkError "type mismatch") 
         | Some p => inl _ (existT (λ s : te, { t : te & tTR s t}) (te_sum s u) 
                              (existT (λ t, tTR (te_sum s u) t) t1 
                                  (trtLeftSum s t1 u t_l (tr_coerce_left u t2 t1 p t_r))))
         end 
     end 
   | trRightSum l r => 
     match (tr_infer l), (tr_infer r) with 
     | inr s, _ => inr _ s
     | _, inr s => inr _ s
     | inl (existT s1 (existT t t_l)), inl (existT s2 (existT u t_r)) => 
         match equal_te2 s2 s1 with 
         | None => inr _ (mkError "type mismatch")
         | Some p => inl _ (existT (λ s : te, { t : te & tTR s t}) s1 
                              (existT (λ t, tTR s1 t) (te_sum t u) 
                                 (trtRightSum s1 t u t_l (tr_coerce_right s2 u s1 p t_r))))
         end 
     end 
   | trProduct  l r => 
     match (tr_infer l), (tr_infer r) with 
     | inr s, _ => inr _ s
     | _, inr s => inr _ s
     | inl (existT s (existT t t_l)), inl (existT u (existT v t_r)) => 
         inl _ (existT (λ s : te, { t : te & tTR s t}) (te_prod s u) 
                  (existT (λ t, tTR (te_prod s u) t) (te_prod t v) 
                      (trtProduct s t u v t_l t_r)))
     end 
   end 
   . 

Definition  DD (A: Type) E (P : A → Type) (d : A + E) : Type 
:= match d with | inr _ => E | inl a => P a end . 

Definition DD_intro : ∀ (A E : Type) (P : A → Type) (d : A + E), (∀ a : A, P a) → DD A E P d
:= λ A,  λ E,  λ P,  λ d,  λ f,  
   match d with 
   | inr e => e 
   | inl a => f a 
   end. 

Definition option_app1  : ∀ A B C E : Type, (A * B) + E →  (A → B → C) → C + E 
:= λ A,  λ B,  λ C,  λ E,  λ d,  λ f,  
   match d with 
   | inr e => inr _ e 
   | inl p => inl _ (f (fst p) (snd p))
   end.

Definition option_app2  : ∀ (A E: Type) 
                            (Q W : A → Type) 
                            (d : {x : A & Q x} + E), 
                            (∀ x : A, Q x → W x) → 
                            DD {x : A & Q x} E (λ p : {x : A & Q x}, W (projT1 p)) d 
:= λ A E Q W d f,  
   match d with 
   | inr e => e 
   | inl p => f (projT1 p) (projT2 p)
   end.

Definition option_app3  : ∀ (A E : Type) 
                            (Q W : A → A → Type) 
                            (d : {x : A & {y : A & Q x y}} + E), 
                            (∀ x y : A, Q x y → W x y) → 
                            DD {x : A & {y : A & Q x y}} 
                               E
                               (λ p : {x : A & {y: A & Q x y}}, 
                                    W (projT1 p) (projT1 (projT2 p))) 
                               d 
:= λ A E Q W d f,  
   match d with 
   | inr e => e 
   | inl p => f (projT1 p) (projT1 (projT2 p)) (projT2 (projT2 p))
   end.


Definition sgr : ∀ s : SG,
       DD {x : te & tSG x} 
          Error 
          (λ p : {x : te & tSG x}, Binary (te_to_Type (projT1 p)))
          (sg_infer s)
:= λ s,  option_app2 _ _ _ _ (sg_infer s) sg_sem. 


End Untyped_CAS. 
