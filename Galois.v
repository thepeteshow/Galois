Require Import FSetProperties Zerob Sumbool DecidableTypeEx.
Require Import Ensembles.
Require Import List.
Require Import Finite_sets.
Require Import FunctionalExtensionality.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.


Module Galois.

Definition reflex {X: Set} (P: X->X->Prop): Prop:=
    forall x: X, (P x x).

Definition antisym {X: Set} (P: X->X->Prop): Prop:=
    forall (x y: X), (P x y)->(P y x)->x=y.

Definition transit {X: Set} (P: X->X->Prop): Prop:=
    forall (x y z: X), (P x y)->(P y z)->(P x z).

Definition poset (X: Set) (order: X->X->Prop): Prop:=
    (reflex order)/\(antisym order)/\(transit order).

Definition trivial_order (X: Set) (x:X) (y:X): Prop:=
    x=y.

Example poset_example: 
poset (nat) (trivial_order nat).
Proof.
unfold poset. split. 
-unfold reflex. intros x. reflexivity.
-split.
+unfold antisym. intros x y H H'. apply H.
+unfold transit. intros x y z. unfold trivial_order. 
intros H H'. rewrite H. apply H'.
Qed.

Inductive Cycleprop {X: Type}:  list X->(X->X->Prop)-> Prop:=
|bicycle (x y: X)(order: X->X->Prop) (H1: ~(x=y)) (H2: order x y): Cycleprop (x::[y]) order
|indcycle (x y:X)(order: X->X->Prop) (l:list X)(H1: x<>y)(H2: order x y)(H3: Cycleprop (y::l) order): Cycleprop (x::y::l) order
.

Definition Cycle {X: Type} (h t: X)(C: list X) (order: X->X->Prop): Prop :=
    Cycleprop (h::C++[t]) order/\h<>t/\order t h.



       
Theorem no_cycles: forall (X: Set) (order: X->X->Prop)(h t: X)(C: list X),
poset X order->~Cycle h t C order.
Proof.
intros. unfold Cycle. unfold not. intros. destruct H0. destruct H1. destruct H. destruct H3. 
induction C. 
-inversion H0.
+apply H3 in H9. apply H9 in H2. contradiction.
+apply H3 in H10. apply H10 in H2. contradiction.
-destruct C. 
*inversion H0. subst. inversion H11. assert (eqn: order h a->order a t->order h t).
{apply H4. }
apply eqn in H10. apply H3 in H10. apply H10 in H2. contradiction. 
assumption. 
inversion H14.
*apply IHC. apply indcycle. 
inversion H0. 
assert (eqn: order a x). inversion H11. assumption. assumption.
unfold not. intros. rewrite<-H12 in eqn. apply H3 in H10. apply H10 in eqn. contradiction.
inversion H0. assert (eqn: order a x). inversion H11. assumption. assumption.
assert(eqn2: order h a->order a x-> order h x). apply H4.
apply eqn2. apply H10. assumption.
inversion H0. subst. inversion H11. unfold app in H9. induction C in H9. 
discriminate. discriminate. apply H14.
Qed.











Definition monotone (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f: X->Y): Prop:=
    poset X xord/\ poset Y yord/\forall x x', xord x x'->yord (f x) (f x').

Definition order_embedding (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f: X->Y): Prop:=
    poset X xord/\ poset Y yord/\forall x x', xord x x'<->yord (f x) (f x').

Theorem order_embedding_injective: forall (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f: X->Y) (x x': X),
    order_embedding X Y xord yord f->f(x)=f(x')->x=x'.
Proof.
    intros. unfold order_embedding in H. destruct H as [H1 H2]. destruct H2 as [H2 H3].
    unfold poset in H2. destruct H2. destruct H1. destruct H4. 
    apply H4; apply H3; rewrite H0; apply H.
    Qed.

Definition surjection (X Y: Set) (f: X->Y): Prop:=
    forall y:Y, exists x, f x=y.

Definition order_isomorphism (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f: X->Y): Prop:=
    order_embedding X Y xord yord f/\surjection X Y f.

Definition composite {X Y Z: Set} (f: X->Y) (g: Y->Z) (x: X): Z:=
    g (f x). 

Theorem monotone_trans: forall (X Y Z: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) 
                              (zord: Z->Z->Prop) (f: X->Y) (g: Y->Z),
monotone X Y xord yord f-> monotone Y Z yord zord g-> monotone X Z xord zord (composite f g).
Proof.
    unfold monotone. intros. split. 
    -apply H.  
    -split. 
    +apply H0.
    +intros. destruct H. destruct H2. apply H3 in H1. destruct H0. destruct H4.
    apply H5 in H1. apply H1.
    Qed.
    
Theorem monotone_assoc: forall (W X Y Z: Set) (word: W->W->Prop) (xord: X->X->Prop) 
                               (yord: Y->Y->Prop) (zord: Z->Z->Prop) (f: W->X) (g: X->Y) (h: Y->Z),
monotone W X word xord f-> monotone X Y xord yord g-> monotone Y Z yord zord h->
composite f (composite g h)=composite (composite f g) h.
Proof.
intros. unfold composite. reflexivity.
Qed.


Theorem isomorphism_trans: forall (X Y Z: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) 
                              (zord: Z->Z->Prop) (f: X->Y) (g: Y->Z),
order_isomorphism X Y xord yord f-> order_isomorphism Y Z yord zord g-> order_isomorphism X Z xord zord (composite f g).
Proof.
unfold order_isomorphism. unfold order_embedding. unfold surjection. intros. split. split.
-apply H.
-split.
+apply H0. 
+intros. split. 
*intros. destruct H. destruct H. destruct H3. apply H4 in H1.
destruct H0. destruct H0. destruct H6. apply H7 in H1. apply H1.
*intros. destruct H. destruct H. destruct H3. unfold composite in H1. 
destruct H0. destruct H0. destruct H6. apply H7 in H1. apply H4 in H1. assumption.
-destruct H0. destruct H. intros. 
assert(exists w:Y, g w = y). apply H1. 
destruct H3.
assert(exists z:X, f z=x). apply H2.
destruct H4. exists x0. unfold composite. rewrite H4. assumption.
Qed.


Definition order_similarity (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop): Prop:=
    poset X xord/\ poset Y yord/\exists f: X->Y, order_isomorphism X Y xord yord f.

Theorem similarity_reflexive: forall (X: Set) (xord: X->X->Prop),
    poset X xord->order_similarity X X xord xord.
Proof.
    intros. unfold order_similarity. split. assumption. split. assumption.
    exists (fun x:X=>x). unfold order_isomorphism. unfold order_embedding.
    split. split. assumption. split. assumption. intros. reflexivity. 
    unfold surjection. intros. exists y. reflexivity.
    Qed.

Theorem similarity_transitive: forall (X Y Z: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (zord: Z->Z->Prop),
order_similarity X Y xord yord->order_similarity Y Z yord zord->order_similarity X Z xord zord.
Proof.
    unfold order_similarity. intros. destruct H. destruct H1. destruct H2.
    destruct H0. destruct H3. destruct H4. split. assumption. split. assumption. 
    exists (composite x x0). 
    assert(eqn: order_isomorphism X Y xord yord x->order_isomorphism Y Z yord zord x0->order_isomorphism X Z xord zord (composite x x0)).
    {apply isomorphism_trans. }
    apply eqn. assumption. assumption.
    Qed.



    
    



Theorem similarity_symmetric: forall (X Y:Set) (xord: X->X->Prop) (yord: Y->Y->Prop),
order_similarity X Y xord yord->order_similarity Y X yord xord.
Proof.
unfold order_similarity. intros. split. apply H. split. apply H.
destruct H. destruct H0. destruct H1 as [g H1].
unfold order_isomorphism in H1. destruct H1. unfold surjection in H2. Admitted.


Definition Galois (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f:X->Y) (g:Y->X): Prop:=
    poset X xord/\poset Y yord/\(forall (x:X) (y:Y), xord x (g y)<->yord (f x) y).

Theorem Galois_trans: forall (X Y Z: Set) (xord: X->X->Prop) (yord: Y->Y->Prop)
                             (zord: Z->Z->Prop) (f:X->Y)(g:Y->X)(h:Y->Z)(i:Z->Y),
    Galois X Y xord yord f g->Galois Y Z yord zord h i->Galois X Z xord zord (composite f h) (composite i g).
Proof.
    unfold Galois. intros. split. apply H. split. apply H0.
    destruct H. destruct H0. destruct H1. destruct H2.
    intros x z. unfold composite. split. 
    -intros. apply H4. apply H3. assumption.
    -intros. apply H3. apply H4. assumption.
    Qed.

Lemma Galois_fact_left: forall  (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f:X->Y) (g:Y->X),
    Galois X Y xord yord f g->forall x:X, xord x (g(f x)).
Proof.
    unfold Galois. intros. destruct H. destruct H0.
    assert (eqn: yord (f x) (f x)). {unfold poset in H0. apply H0. }
    apply H1 in eqn. assumption. Qed.

Lemma Galois_fact_right: forall  (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f:X->Y) (g:Y->X),
    Galois X Y xord yord f g->forall y:Y, yord (f(g y)) y.
Proof.
    unfold Galois. intros. destruct H. destruct H0.
    assert (eqn: xord (g y)(g y)). {unfold poset in H. apply H. }
    apply H1 in eqn. assumption. Qed.

Theorem Galois_reform: forall (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f:X->Y) (g:Y->X),
    Galois X Y xord yord f g <->(monotone X Y xord yord f)/\(monotone Y X yord xord g)
    /\(forall x:X, xord x (g (f x)))/\(forall y:Y, yord (f(g y)) y).
Proof.
    intros. unfold Galois. unfold monotone. split. 
    -intros. split. 
    +split. apply H. split. apply H.
    intros. destruct H. destruct H1. apply H2. 
    assert(eqn: xord x' (g(f x'))). 
    {apply Galois_fact_left with (yord:=yord). unfold Galois. split. apply H. split. assumption. assumption. }
    destruct H. destruct H3. apply H4 with (y:=x').
    assumption. assumption.
    +split. split. apply H. split.
    *apply H.
    *intros. destruct H. destruct H1. apply H2. 
    assert(eqn: yord (f(g x)) x). apply Galois_fact_right with (xord:=xord). 
    unfold Galois. split. assumption. split. assumption. assumption.
    destruct H1. destruct H3. apply H4 with (y:=x). 
    assumption. assumption.
    *split. apply Galois_fact_left with (yord:=yord). unfold Galois. split. apply H. split. apply H.
    apply H.
    apply Galois_fact_right with (xord:=xord). unfold Galois. split. apply H. split.
    apply H. apply H.
    -intros. destruct H. destruct H0. split. apply H. split. apply H. 
    intros. split.
    +intros. destruct H. destruct H3. apply H4 in H2. destruct H1. 
    destruct H3. destruct H6. apply H7 with (y:=(f(g y))). assumption. apply H5.
    +intros. destruct H0. destruct H3. apply H4 in H2. destruct H1.
    destruct H3. destruct H6. apply H7 with (y:=(g(f x))). apply H1. assumption.
    Qed.

Theorem Galois_right_adjoint: forall (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f:X->Y)(g:Y->X)(h:Y->X),
    Galois X Y xord yord f g->Galois X Y xord yord f h->g=h.
Proof.
    intros. apply functional_extensionality. intros y.
    assert (eqn: xord (g y) (h y)). 
    -apply H0. apply Galois_fact_right with (xord:= xord). assumption.
    -assert(eqn': xord (h y) (g y)).
    +apply H. apply Galois_fact_right with (xord:= xord). assumption.
    +apply H. assumption. assumption.
    Qed.

Theorem Galois_left_adjoint: forall (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f:X->Y)(g:X->Y)(h:Y->X),
    Galois X Y xord yord f h->Galois X Y xord yord g h->f=g.
Proof.
    intros. apply functional_extensionality. intros x.
    assert (eqn: yord (f x)(g x)).
    -apply H. apply Galois_fact_left with (yord:= yord). assumption.
    -assert (eqn': yord (g x)(f x)).
    +apply H0. apply Galois_fact_left with (yord:=yord). assumption.
    +apply H. assumption. assumption.
    Qed.

Theorem Galois_domains: forall (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f:X->Y)(g:Y->X),
    Galois X Y xord yord f g->composite f (composite g f)=f/\composite g (composite f g)=g.
Proof.
    intros. split. apply functional_extensionality.
    unfold composite. intros. assert (eqn: yord (f(g(f x))) (f x)). 
    {apply Galois_fact_right with (xord:=xord). assumption. }
    assert (eqn': yord (f x) (f(g(f x)))). 
    {apply Galois_reform in H. apply H. apply H. }
    apply H. assumption. assumption.
    apply functional_extensionality.
    unfold composite. intros.
    apply H. apply Galois_reform in H. apply H. apply H.
    apply H. destruct H. destruct H0. apply H0.
    Qed.


Theorem Galois_fixed_point: forall (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f:X->Y)(g:Y->X),
    Galois X Y xord yord f g->(forall y:Y, (exists x:X, f x=y)<->f (g y)=y)
                            /\(forall x:X, (exists y:Y, g y=x)<->g(f x)=x).
Proof.
    intros. split. 
    -split.
    +intros. destruct H0. rewrite<-H0. apply Galois_domains in H. 
    assert(eqn: composite f (composite g f) x=f(g(f x))). {reflexivity. }
    rewrite<-eqn. destruct H. rewrite H. reflexivity.
    +exists (g y). assumption.
    -split.
    +intros. destruct H0 as [y H']. rewrite <- H'. apply Galois_domains in H.
    assert (eqn: composite g (composite f g) y= g(f(g y))). {reflexivity. }
    rewrite<-eqn. destruct H. rewrite H0. reflexivity.
    +exists (f x). assumption.
    Qed.
    
    
Theorem Galois_images: forall (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f:X->Y)(g:Y->X),
Galois X Y xord yord f g->(forall y:Y, (exists x:X, f x=y)<->exists y':Y, f (g y')=y)
                        /\(forall x:X, (exists y:Y, g y=x)<->exists x':X, g(f x')=x).
Proof.
    intros. apply Galois_fixed_point in H. split. 
    -intros. split.
    +intros. destruct H0. exists y.  apply H. exists x. assumption.
    +intros. destruct H0. exists (g x). assumption.
    -intros. split.
    +intros. destruct H0. exists x. apply H. exists x0. assumption.
    +intros. destruct H0. exists (f x0). assumption.
    Qed.
    
    
Definition Closure (X:Set) (order: X->X->Prop) (f:X->X): Prop:=
    poset X order /\(forall x y, (order x (f x))/\(order x y->order (f x) (f y))/\f x=f(f x)).


Theorem closure_composite: forall (X Y: Set) (xord: X->X->Prop) (yord: Y->Y->Prop) (f:X->Y)(g:Y->X),
    Galois X Y xord yord f g->Closure X xord (composite f g).
Proof.
    intros. unfold Closure. unfold composite. 
    split. apply H.
    split. apply Galois_fact_left with (yord:=yord). assumption.
    split. apply Galois_reform in H. intros. apply H. apply H. assumption.
    apply Galois_domains in H.  
    assert(eqn: composite f (composite g f) x = f x). 
    {destruct H. rewrite H. reflexivity. }
    unfold composite in eqn. rewrite eqn. reflexivity.
    Qed.

    Definition reflex' {X: Type} (P: X->X->Prop)(Q: X->Prop): Prop:=
        forall x: X, Q x->(P x x).
    
    Definition antisym' {X: Type} (P: X->X->Prop)(Q: X->Prop): Prop:=
        forall (x y: X), Q x->Q y->(P x y)->(P y x)->x=y.
    
    Definition transit' {X: Type} (P: X->X->Prop)(Q: X->Prop): Prop:=
        forall (x y z: X), Q x->Q y->Q z->(P x y)->(P y z)->(P x z).
    
    Definition posubset (X: Type) (order: X->X->Prop)(Q: X->Prop): Prop:=
        (reflex' order Q)/\(antisym' order Q)/\(transit' order Q).

    Fixpoint even (n: nat): Prop:=
    match n with
    |0=>True
    |S n'=>match n' with
           |0=>False 
           |S n''=> even n''
           end 
    end.

    Example example_reprise: 
    posubset nat (trivial_order nat) even.
    Proof.
    unfold posubset. split.
    -unfold reflex'. intros. unfold trivial_order. reflexivity.
    -split.
    +unfold antisym'. intros. apply H1.
    +unfold transit'. unfold trivial_order. intros. rewrite H2. apply H3.
    Qed.
    
    Theorem subset_restriction: forall (X: Type)(P Q: X->Prop)(ord: X->X->Prop),
        (forall x, Q x->P x)->posubset X ord P->posubset X ord Q.
    Proof.
        intros. unfold posubset. split. 
        -unfold reflex'. intros. apply H0. apply H. assumption.
        -split.
        +unfold antisym'. intros. apply H0. apply H. assumption. apply H. assumption. assumption. assumption.
        +unfold transit'. intros. unfold posubset in H0. destruct H0. 
        destruct H6. unfold transit' in H7.
        apply H in H1. apply H7 with (y:=y)(z:=z) in H1. 
        assumption. apply H. assumption. apply H. assumption. assumption. assumption.
        Qed.

    
    Definition monotone' (X Y: Type)(P:X->Prop)(Q:Y->Prop)(xord: X->X->Prop) (yord: Y->Y->Prop) (f: X->Y): Prop:=
        posubset X xord P/\ posubset Y yord Q/\(forall x, P x->Q (f x))/\forall x x', P x->P x'->xord x x'->yord (f x) (f x').
    
    Definition order_embedding' (X Y: Type) (P:X->Prop)(Q:Y->Prop)(xord: X->X->Prop) (yord: Y->Y->Prop) (f: X->Y): Prop:=
        posubset X xord P/\ posubset Y yord Q/\(forall x, P x<->Q (f x))/\forall x x', P x->P x'->xord x x'<->yord (f x) (f x').

    
    Theorem order_embedding_injective': forall (X Y: Type)(P:X->Prop)(Q:Y->Prop)(xord: X->X->Prop) (yord: Y->Y->Prop) (f: X->Y) (x x': X),
        order_embedding' X Y P Q xord yord f->P x->P x'->f(x)=f(x')->x=x'.
    Proof.
        intros. unfold order_embedding' in H. destruct H. destruct H3. destruct H4.
        unfold poset in H. destruct H. destruct H6. destruct H3. destruct H8. apply H6.
        assert (eqn: xord x x' <-> yord (f x) (f x')); try apply H5; assumption. assumption. apply H5. assumption; assumption.
        assumption. rewrite H2. apply H3. apply H4. assumption.
        apply H5. assumption; assumption. assumption. rewrite H2. apply H3. apply H4. assumption.
        Qed. 
        

    
    Definition subs_surj (X Y: Type)(P:X->Prop)(Q:Y->Prop) (f: X->Y): Prop:=
        forall y:Y, Q y->exists x, P x/\f x=y.
        
    Definition order_isomorphism' (X Y: Type) (P:X->Prop)(Q:Y->Prop)(xord: X->X->Prop) (yord: Y->Y->Prop) (f: X->Y): Prop:=
        order_embedding' X Y P Q xord yord f/\subs_surj X Y P Q f.
    
    Theorem monotone_trans': forall (X Y Z: Set) (P:X->Prop)(Q:Y->Prop)(R:Z->Prop)(xord: X->X->Prop) (yord: Y->Y->Prop) 
        (zord: Z->Z->Prop) (f: X->Y) (g: Y->Z),
        monotone' X Y P Q xord yord f-> monotone' Y Z Q R yord zord g-> monotone' X Z P R xord zord (composite f g).
    Proof.
        unfold monotone'. intros. split. apply H. split. apply H0.
        split; intros. apply H0. apply H. assumption.
        apply H0. apply H. assumption. apply H. assumption. apply H.
        assumption. assumption. assumption.
        Qed.
    
    Theorem monotone_assoc': forall (W X Y Z: Set) (O: W->Prop)(P:X->Prop)(Q:Y->Prop)(R:Z->Prop)
        (word: W->W->Prop) (xord: X->X->Prop) (yord: Y->Y->Prop) (zord: Z->Z->Prop) (f: W->X) (g: X->Y) (h: Y->Z),
        monotone' W X O P word xord f-> monotone' X Y P Q xord yord g-> monotone' Y Z Q R yord zord h->
        composite f (composite g h)=composite (composite f g) h/\monotone' W Z O R word zord (composite f (composite g h)).
    Proof.
        intros. split. unfold composite. reflexivity.
        apply monotone_trans' with (Y:=X)(Q:=P)(yord:=xord)(f:=f)(g:=(composite g h)).
        assumption.
        apply monotone_trans' with (Y:=Y)(Q:=Q)(yord:=yord).
        assumption. assumption.
        Qed.

    Definition inimage (X Y: Set)(f:X->Y)(y:Y):Prop:=
        exists x, f x=y.

    Theorem embedding_isomorphism: forall (X Y: Set)(P:X->Prop)(Q:Y->Prop)(xord:X->X->Prop)(yord:Y->Y->Prop)(f:X->Y),
        order_embedding' X Y P Q xord yord f->order_isomorphism' X Y P (fun y: Y=>Q y/\(exists x, f x=y)) xord yord f.
    Proof.
         unfold order_isomorphism'. unfold order_embedding'. unfold posubset. unfold reflex'. unfold antisym'. unfold transit'.
        intros. split.
        -split. apply H. split. split. intros. apply H. apply H0.
        split. intros. apply H. apply H0. apply H1. assumption. assumption.
        intros. apply H with (y:=y). apply H0. apply H1. apply H2. apply H3. apply H4. 
        split. split. intros. split. apply H. apply H0.
        exists x. reflexivity. intros. apply H. apply H0.
        apply H.
        -unfold subs_surj. intros. destruct H0. destruct H1. rewrite<-H1 in H0. apply H in H0. 
        exists x. split. assumption. assumption.
        Qed.
    
    Definition inclusion_poset (X:Type):Type:=
        X->Prop.
    
    Definition inclusion_order (X:Type)(P Q:inclusion_poset X):Prop:=
        forall x, P x->Q x.
    
    Axiom propositional_equality: forall (X:Set) (P Q:X->Prop),
   P=Q <-> (forall x:X, P x<->Q x).

    Theorem inclusion_sound: forall {X:Set} (P:(inclusion_poset X)->Prop), 
        posubset (inclusion_poset X) (inclusion_order X) P.
    Proof.
        intros. unfold posubset. unfold inclusion_order. split. 
        -unfold reflex'. intros. assumption.
        -split.
        +unfold antisym'. intros. apply propositional_equality. intros.
        split. apply H1. apply H2.
        +unfold transit'. intros. apply H3. apply H2. assumption.
        Qed.
        

    Definition typical_helper (X:Type) (P:X->Prop) (ord:X->X->Prop) (x y:X): Prop:=
        P x/\P y/\ord y x.


        Definition typical_helper2 (X:Type) (P:X->Prop) (ord:X->X->Prop) (y:inclusion_poset X): (Prop):=
           exists x:X, P x/\y=typical_helper X P ord x.

    Theorem inclusion_typical: forall (X:Set) (P:X->Prop) (ord:X->X->Prop),
        posubset X ord P->exists (Y:Set)(Q:(inclusion_poset Y)->Prop)(f:X->inclusion_poset Y), 
        order_isomorphism' X (inclusion_poset Y) P Q ord (inclusion_order Y) f.
    Proof.
        intros. exists X. exists (typical_helper2 X P ord). exists (typical_helper X P ord).
        unfold order_isomorphism'. unfold order_embedding'. unfold subs_surj.
        split. split. assumption. split. apply inclusion_sound. split.
        -split.
        +intros. unfold typical_helper2. exists x. split. assumption. reflexivity.
        +unfold typical_helper2. intros.
        destruct H0. destruct H0. 
        apply propositional_equality with (x:=x0) in H1.  
        unfold typical_helper in H1. destruct H1.
        destruct H2. split. assumption. split. assumption. apply H. assumption.
        assumption.
        -intros. split; unfold inclusion_order; unfold typical_helper; intros.
        + split. assumption. split. apply H3. apply H with (y:=x).
        apply H3. apply H3. assumption. apply H3. assumption.
        +assert (eqn: P x/\P x/\ord x x->P x'/\P x/\ord x x').
        {apply H2. } destruct eqn. split. assumption. split. assumption. apply H. assumption.
        apply H4.
        -unfold inclusion_poset. unfold typical_helper2. intros. destruct H0.
        exists x. split. apply H0. destruct H0. rewrite H1. reflexivity.
        Qed.
        

        
        
        
    
        
    

    

    

    



    
    



 










    