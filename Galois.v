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

Definition composite {X Y Z: Type} (f: X->Y) (g: Y->Z) (x: X): Z:=
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
    +split. split. apply H.
    split. apply H. Admitted. (*
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
    Qed.*)

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
        posubset X xord P/\ posubset Y yord Q/\(forall x, P x->Q (f x))/\forall x x', P x->P x'->xord x x'<->yord (f x) (f x').

    
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

    Theorem isomorphism_trans': forall (X Y Z: Set)(P:X->Prop)(Q:Y->Prop)(R:Z->Prop)
                                (xord:X->X->Prop)(yord: Y->Y->Prop)(zord:Z->Z->Prop)(f: X->Y)(g:Y->Z),
        order_isomorphism' X Y P Q xord yord f->order_isomorphism' Y Z Q R yord zord g->
        order_isomorphism' X Z P R xord zord (composite f g).
    Proof.
        unfold order_isomorphism'. unfold order_embedding'. unfold subs_surj. intros.
        split. split. apply H. split. apply H0.
        split. intros. apply H0. apply H. assumption.
        intros. split. intros. apply H0; try (apply H; assumption).
        intros. apply H; try assumption. apply H0; try (apply H; assumption). assumption.
        intros. apply H0 in H1. destruct H1. destruct H1.
        apply H in H1. destruct H1. exists x0. split.
        apply H1. destruct H1. rewrite<-H3 in H2. assumption.
        Qed.

    
    Definition inimage (X Y: Set)(f:X->Y)(y:Y):Prop:=
        exists x, f x=y.

    Theorem embedding_isomorphism: forall (X Y: Set)(P:X->Prop)(Q:Y->Prop)(xord:X->X->Prop)(yord:Y->Y->Prop)(f:X->Y),
        order_embedding' X Y P Q xord yord f->order_isomorphism' X Y P (fun y: Y=>Q y/\(exists x, P x/\f x=y)) xord yord f.
    Proof.
         unfold order_isomorphism'. unfold order_embedding'. unfold posubset. unfold reflex'. unfold antisym'. unfold transit'.
        intros. split.
        -split. apply H. split. split. intros. apply H. apply H0.
        split. intros. apply H. apply H0. apply H1. assumption. assumption.
        intros. apply H with (y:=y). apply H0. apply H1. apply H2. apply H3. apply H4. 
        split. split. intros. apply H. apply H0.
        exists x. split. assumption. reflexivity. intros. apply H. apply H0.
        apply H1.
        -unfold subs_surj. intros. destruct H0. destruct H1.
        destruct H1. exists x. split. assumption. assumption.
        Qed.
    
    Definition inclusion_poset (X:Type):Type:=
        X->Prop.
    
    Definition inclusion_order (X:Type)(P Q:inclusion_poset X):Prop:=
        forall x, P x->Q x.
    
    Axiom propositional_equality: forall (X:Type) (P Q:X->Prop),
   P=Q <-> (forall x:X, P x<->Q x).
    
    Theorem inclusion_sound: forall {X:Type} (P:(inclusion_poset X)->Prop), 
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
        -intros. unfold typical_helper2. exists x. split. assumption. reflexivity.
        -intros. split; unfold inclusion_order; unfold typical_helper; intros.
        + split. assumption. split. apply H3. apply H with (y:=x).
        apply H3. apply H3. assumption. apply H3. assumption.
        +assert (eqn: P x/\P x/\ord x x->P x'/\P x/\ord x x').
        {apply H2. } destruct eqn. split. assumption. split. assumption. apply H. assumption.
        apply H4.
        -unfold inclusion_poset. unfold typical_helper2. intros. destruct H0.
        exists x. split. apply H0. destruct H0. rewrite H1. reflexivity.
        Qed.


    Definition Galois' (X Y: Type)(P:X->Prop)(Q:Y->Prop)(xord:X->X->Prop)(yord: Y->Y->Prop)(f:X->Y)(g:Y->X): Prop:=
        posubset X xord P/\posubset Y yord Q/\
        forall (x:X) (y:Y), (P x->Q (f x))/\(Q y->P(g y))/\(P x->Q y->(xord x (g y)<->yord (f x) y)).
    
    Theorem Galois_trans': forall (X Y Z: Set) (P:X->Prop)(Q:Y->Prop)(R:Z->Prop)
        (xord: X->X->Prop) (yord: Y->Y->Prop)(zord: Z->Z->Prop) (f:X->Y)(g:Y->X)(h:Y->Z)(i:Z->Y),
        Galois' X Y P Q xord yord f g->Galois' Y Z Q R yord zord h i->Galois' X Z P R xord zord (composite f h) (composite i g).
    Proof.
        unfold Galois'. intros. split. apply H. split. apply H0.
        intros. split. intros. destruct H. destruct H2.
        unfold composite.
        apply H0 . assumption. apply H3. apply f. assumption. assumption.
        intros. split; intros.
        -destruct H. destruct H2. destruct H0. destruct H4. destruct H5 with (x:=i y)(y:=y). 
        destruct H7. apply H7 in H1. destruct H3 with (x:=x)(y:=i y).
        destruct H10. apply H10 in H1. assumption.
        -destruct H. destruct H3. destruct H4 with (x:=x)(y:=i y). destruct H6.
          assert (eqn: P x). assumption. apply H7 in H1. 
          destruct H0. destruct H8. destruct H9 with (x:=f x)(y:=y). 
         destruct H11.
         assert (eqn': R y). assumption.
         apply H11 in H2. apply H5 in eqn. apply H12 in eqn.
         split; intros.  apply eqn. apply H1. assumption.
         apply H1. apply eqn. assumption. assumption.
         destruct H0. destruct H8. destruct H9 with (x:=f x)(y:=y). 
         destruct H11. apply H11 in H2. assumption.
         Qed.   
        

    Lemma Galois_fact_A: forall (X Y: Type)(P:X->Prop)(Q:Y->Prop)(xord:X->X->Prop)(yord:Y->Y->Prop)(f:X->Y)(g:Y->X),
        Galois' X Y P Q xord yord f g->forall x:X, P x->xord x (g (f x)).
    Proof. 
        intros. destruct H. destruct H1. destruct H2 with (x:=x)(y:=f x).
        destruct H4.
        assert (eqn: P x->Q (f x)). assumption.
        apply H5 in H3. apply H3. apply H1. apply eqn. assumption. assumption. assumption.
        Qed.

    Lemma Galois_fact_B: forall (X Y: Type)(P:X->Prop)(Q:Y->Prop)(xord:X->X->Prop)(yord:Y->Y->Prop)(f:X->Y)(g:Y->X),
        Galois' X Y P Q xord yord f g->forall y:Y, Q y->yord (f (g y)) y.
    Proof.
        intros. destruct H. destruct H1. destruct H2 with (x:= g y)(y:=y).
        destruct H4.
        assert (eqn: Q y). assumption.
        apply H4 in H0. apply H5 in H0. apply H0. apply H.
        apply H4. assumption. assumption.
        Qed.

    
    Theorem galois_reform': forall (X Y: Type)(P:X->Prop)(Q:Y->Prop)(xord:X->X->Prop)(yord:Y->Y->Prop)(f:X->Y)(g:Y->X),
        Galois' X Y P Q xord yord f g<->(monotone' X Y P Q xord yord f)/\(monotone' Y X Q P yord xord g)
        /\(forall x:X, P x->xord x (g (f x)))/\(forall y:Y, Q y->yord (f(g y)) y).
    Proof.
        intros. split; intros. split.
        -unfold monotone'. split. apply H. split. apply H.
        split; unfold Galois' in H. intros. destruct H. destruct H1.
        destruct H2 with (x:=x)(y:= (f x)). apply H3. assumption.
        intros. destruct H. destruct H3. destruct H4 with (x:=x)(y:=(f x')).
        destruct H6. assert (eqn: Q(f x')). apply H4. apply f. assumption. assumption.
        apply H7. assumption. assumption. apply H with (y:=x'); try assumption.
        apply H6. assumption.
        apply Galois_fact_A with (P:=P)(Q:=Q)(yord:=yord).
        split. apply H. split. apply H3. apply H4. apply H1.
        -split.
        +unfold monotone'. split. apply H. split. apply H. split. 
        intros. apply H. apply g. assumption. assumption.
        intros. apply H with (x:=g x)(y:=x').
        apply H. apply g. assumption. assumption. assumption.
        apply H with (y:=x). apply H. assumption. apply H.
        apply g; assumption. assumption. assumption. assumption.
        apply Galois_fact_B with (P:=P)(Q:=Q)(xord:=xord); assumption. assumption.
        +split.
        *intros. apply Galois_fact_A with (P:=P)(Q:=Q)(yord:=yord); assumption.
        *intros. apply Galois_fact_B with (P:=P)(Q:=Q)(xord:=xord); assumption.
        -split. apply H. split. apply H. intros. split. apply H. split. apply H.
        intros. split; intros.
        +assert (eqn: yord (f x)(f (g y))). apply H; try assumption.
        apply H. assumption.
        apply H with (y:=(f(g y))); try (apply H; assumption).
        apply H. apply H. assumption. assumption. assumption.
        +assert (eqn: xord (g(f x)) (g y)). apply H; try assumption.
        apply H. assumption.
        apply H with (y:=(g(f x))); try (apply H; assumption);
        try assumption. apply H. apply H. assumption.
        Qed.

        Theorem Galois_left_adjoint': forall (X Y: Type)(P:X->Prop)(Q:Y->Prop)(xord:X->X->Prop)(yord:Y->Y->Prop)(f:X->Y)(g:Y->X)(h:Y->X),
            Galois' X Y P Q xord yord f g->Galois' X Y P Q xord yord f h->forall y:Y, (Q y->g y=h y).
        Proof.
            intros. 
            assert (e1: xord (g y) (h y)). apply H0. apply H. apply g.
            assumption. assumption. assumption. apply H; try assumption. 
            apply H. apply g. assumption. assumption. destruct H. 
            apply H. apply H2. apply g. assumption. assumption.
            assert (e2: xord (h y) (g y)). apply H. apply H0; try assumption.
            apply g. assumption. assumption. apply H0. apply H0; try apply g; assumption.
            assumption. destruct H0. apply H0. apply H2; try apply h; assumption.
            apply H. apply H; try apply g; assumption.
            apply H0; try apply g; assumption.
            assumption. assumption. Qed.


        Theorem Galois_right_adjoint': forall (X Y: Type)(P:X->Prop)(Q:Y->Prop)(xord:X->X->Prop)(yord:Y->Y->Prop)(f:X->Y)(g:X->Y)(h:Y->X),
            Galois' X Y P Q xord yord g h->Galois' X Y P Q xord yord f h->forall x:X, (P x->f x=g x).
        Proof.
            intros. assert (eqn: Q (g x)/\Q (f x)).
            split; [apply H|apply H0]; try apply f; assumption. destruct eqn.
            assert (e1: yord (f x)(g x)).
            apply H0; try assumption. apply H; try assumption.
            destruct H. destruct H4. apply H4; assumption.
            assert (e2: yord (g x) (f x)).
            apply H; try assumption. apply H0; try assumption.
            destruct H0. destruct H4. apply H4; assumption.
            apply H; assumption.
            Qed.
            
        Theorem Galois_composition: forall (X Y: Type)(P:X->Prop)(Q:Y->Prop)(xord:X->X->Prop)(yord:Y->Y->Prop)(f:X->Y)(g:Y->X)(x:X)(y:Y),
            Galois' X Y P Q xord yord f g->(P x->f x=f(g(f x)))/\(Q y->g y=g(f(g y))).
        Proof.
            intros. apply galois_reform' in H. split; intros. 
            assert (eqn: yord (f x)(f(g(f x)))).
            apply H; try apply H; try assumption. apply H. assumption.
            assert (eqn': yord (f(g(f x))) (f x)). apply H. apply H. assumption.
            destruct H. destruct H1. destruct H1. 
            apply H1; try assumption. apply H. assumption.
            apply H. apply H3. apply H. assumption.
            assert (eqn: xord (g y)(g(f(g y)))). apply H. apply H. assumption.
            assert (eqn': xord (g(f(g y)))(g y)).
            apply H; try apply H; try assumption. apply H. assumption.
            apply galois_reform' in H. apply H; try assumption; try apply H; try assumption.
            apply H. assumption. apply H; assumption.
            Qed.

        Theorem Galois_fixed_point': forall (X Y: Type)(P:X->Prop)(Q:Y->Prop)(xord:X->X->Prop)(yord:Y->Y->Prop)(f:X->Y)(g:Y->X)(x:X)(y:Y),
            Galois' X Y P Q xord yord f g->(Q y->((exists x:X, P x/\f x=y)<->y=f(g y)))/\
                                           (P x->((exists y:Y, Q y/\g y=x)<->x=g(f x))).
        Proof.
            intros. split; intros. 
            -split; intros.
            +destruct H1. destruct H1. rewrite<-H2. 
            apply Galois_composition with (P:=P)(Q:=Q)(xord:=xord)(yord:=yord); assumption.
            +exists (g y). split. apply H; assumption. symmetry. assumption.
            -split; intros.
            +destruct H1. destruct H1. rewrite<-H2.
            apply Galois_composition with (P:=P)(Q:=Q)(xord:=xord)(yord:=yord); assumption.
            +exists (f x). split. apply H; assumption. symmetry. assumption.
            Qed.

        Theorem Galois_images': forall (X Y: Set) (P:X->Prop)(Q:Y->Prop)(xord: X->X->Prop) (yord: Y->Y->Prop) (f:X->Y)(g:Y->X)(x:X)(y:Y),
            Galois' X Y P Q xord yord f g->(Q y->(exists x:X, P x/\f x=y)<->(exists y':Y, Q y'/\f (g y')=y))
                                    /\(P x-> (exists y:Y, Q y/\g y=x)<->(exists x':X, P x'/\g(f x')=x)).
        Proof.
            intros. split; intros. 
            -split; intros; destruct H1; destruct H1.
            +exists (f x0). split.
            * apply H; assumption.
            *rewrite <-H2. symmetry. apply Galois_composition with (P:=P)(Q:=Q)(xord:=xord)(yord:=yord); assumption.
            +exists (g x0). split.
            *apply H; assumption.
            *assumption.
            -split; intros; destruct H1; destruct H1.
            +exists (g x0). split.
            * apply H; assumption.
            *rewrite<-H2. symmetry. apply Galois_composition with (P:=P)(Q:=Q)(xord:=xord)(yord:=yord); assumption.
            + exists (f x0). split.
            *apply H; assumption.
            *assumption.
            Qed.

        
        Definition double_image (X Y: Set)(P:X->Prop)(f:X->Y)(g:Y->X)(x:X):Prop:=
            P x/\exists x':X, P x'/\g(f x')=x.
    
        Theorem Galois_isomorphism: forall (X Y: Set) (P:X->Prop)(Q:Y->Prop)(xord: X->X->Prop) (yord: Y->Y->Prop) (f:X->Y)(g:Y->X),
            Galois' X Y P Q xord yord f g->order_isomorphism' X Y (double_image X Y P f g) (double_image Y X Q g f) xord yord f.
        Proof.
            intros. unfold order_isomorphism'. unfold order_embedding'. 
            split. split. apply subset_restriction with (P:=P).
            intros. apply H0. apply H. 
            split. apply subset_restriction with (P:=Q).
            intros. apply H0. apply H.
            split. unfold double_image. split; intros.
            -apply H. apply f. apply x. apply H0.
            -destruct H0. destruct H1. exists (f x0).
            split. apply H. apply f. assumption. apply H1.
            destruct H1. rewrite H2. reflexivity.
            -intros. split; intros.
            +apply galois_reform' in H. apply H. apply H0. apply H1. apply H2.
            +apply galois_reform' in H. apply H in H2. 
            destruct H0. destruct H3. assert (eqn: x=g(f x)).
            apply Galois_fixed_point' with (P:=P)(Q:=Q)(xord:=xord)(yord:=yord);
            try assumption. apply f. assumption. apply galois_reform'. assumption.
            exists (f x0). split. apply H. apply H3. apply H3.
            assert(eqn': x'=g(f x')).
            apply Galois_fixed_point' with (P:=P)(Q:=Q)(xord:=xord)(yord:=yord).
            apply f. assumption. apply galois_reform'. assumption.
            apply H1. destruct H1. destruct H4. exists (f x1).
            split. apply H. apply H4. apply H4.
            rewrite eqn. rewrite eqn'. assumption.
            apply H. apply H0. apply H. apply H1.
            -unfold subs_surj. unfold double_image. intros.
            destruct H0. destruct H1. exists (g x). split. split.
            apply H. apply g. apply x. apply H1.
            exists (g x). split.
            apply H. apply g. apply x. apply H1.
            symmetry. apply Galois_composition with (P:=P)(Q:=Q)(xord:=xord)(yord:=yord).
            apply g. apply x. apply H. apply H1. apply H1.
            Qed.

        Definition Closure' (X:Set) (P:X->Prop)(order: X->X->Prop) (f:X->X): Prop:=
            posubset X order P/\(forall x y, P x->P y->(order x (f x))/\(order x y->order (f x) (f y))/\f x=f(f x)).

        Theorem closure_composite': forall (X Y: Set) (P:X->Prop)(Q:Y->Prop)(xord: X->X->Prop) (yord: Y->Y->Prop) (f:X->Y)(g:Y->X),
            Galois' X Y P Q xord yord f g->Closure' X P xord (composite f g).
        Proof.
            intros. unfold Closure'. split. apply H. intros.
            split. unfold composite. apply Galois_fact_A with (P:=P)(Q:=Q)(yord:=yord);
            assumption. split; intros.
            unfold composite. apply galois_reform' in H. apply H; apply H; assumption.
            unfold composite. apply Galois_composition with (P:=P)(Q:=Q)(xord:=xord)(yord:=yord);
            try assumption. apply H. apply f. assumption. assumption.
        Qed.

        Definition subset_function (X Y: Type)(r:X->Y->Prop)(Q:Y->Prop)(P:X->Prop)(y:Y): Prop:=
            Q y/\forall x:X, P x->r x y.
        
        Definition subset_discriminant (X Y: Type)(P:X->Prop)(Q:Y->Prop)(r:X->Y->Prop)(B:inclusion_poset Y):Prop:=
            exists (A:inclusion_poset X), (forall x, A x->P x)/\B=subset_function X Y r Q A.

        Definition invert {X Y: Type}(r:X->Y->Prop)(y:Y)(x:X):Prop:=
            r x y.
        
        Definition inclusion_disorder (X:Type)(P Q:inclusion_poset X):Prop:=
            inclusion_order X Q P.

        Theorem Galois_instance: forall (X Y:Type)(P:X->Prop)(Q:Y->Prop)(r:X->Y->Prop)(s:Y->X->Prop),
            Galois' (inclusion_poset X) (inclusion_poset Y) (subset_discriminant Y X Q P (invert r))
                    (subset_discriminant X Y P Q r)(inclusion_order X)(inclusion_disorder Y)(subset_function X Y r Q)(subset_function Y X (invert r) P).
        Proof.
            intros. unfold Galois'. split. 
            apply inclusion_sound. split.
            unfold inclusion_disorder. split.
            unfold reflex'. intros. unfold inclusion_order. intros. assumption.
            split. unfold antisym'. unfold inclusion_order. intros. 
            apply propositional_equality. intros. split; intros.
            apply H2. assumption. apply H1. assumption.
            unfold transit'. unfold inclusion_order. intros.
            apply H2. apply H3. assumption.
            intros. unfold subset_discriminant. split; intros.
            destruct H. destruct H. exists x. split; intros. 
            rewrite H0 in H1. apply H1. reflexivity.
            split; intros. destruct H. destruct H.
            exists y. split; intros. rewrite H0 in H1. 
            apply H1. reflexivity. 
            unfold inclusion_disorder. unfold inclusion_order. unfold subset_function.
            split; intros. destruct H0. destruct H0. split.
             rewrite H3 in H2. apply H2.
            intros. apply H1 in H4. apply H4. assumption.
            split; intros. destruct H. destruct H.
            rewrite H3 in H2. apply H2.
            apply H1 in H3. apply H3. assumption.
            Qed.


        Inductive orthoprod (X Y:Type) : Type :=
            | pair (x:X)(y:Y).
        
        Definition fst (X Y:Type)(p: orthoprod X Y) : X :=
            match p with 
            | pair _ _ x y=>x
            end.
        
        Definition snd (X Y:Type)(p: orthoprod X Y) : Y :=
            match p with 
            | pair _ _ x y=>y
            end.
        Theorem product_terms: forall (X Y:Type)(p:orthoprod X Y),
            p=pair X Y (fst X Y p)(snd X Y p).
        Proof.
            intros. destruct p. reflexivity. Qed.


        Definition compord (X Y:Type)(xord:X->X->Prop)(yord:Y->Y->Prop)(p1:orthoprod X Y)(p2: orthoprod X Y):Prop:=
            xord (fst X Y p1)(fst X Y p2)/\yord (snd X Y p1)(snd X Y p2).

        Definition compordor (X Y:Type)(xord:X->X->Prop)(yord:Y->Y->Prop)(p1:orthoprod X Y)(p2: orthoprod X Y):Prop:=
            xord (fst X Y p1)(fst X Y p2)\/yord (snd X Y p1)(snd X Y p2).
        
        Definition compprop (X Y:Type)(P:X->Prop)(Q:Y->Prop)(p:orthoprod X Y):Prop:=
            P (fst X Y p)/\Q (snd X Y p).

        Definition compfunc (W X Y Z:Type)(f:X->W)(h:Y->Z)(p:orthoprod X Y):orthoprod W Z:=
            pair W Z (f (fst X Y p))(h (snd X Y p)).

        Theorem orthogonal_composition: forall (W X Y Z:Type)(P:X->Prop)(Q:Y->Prop)(R:W->Prop)(S:Z->Prop)
                                                   (word:W->W->Prop)(xord:X->X->Prop)(yord:Y->Y->Prop)(zord:Z->Z->Prop)
                                                   (f:X->W)(g:W->X)(h:Y->Z)(i:Z->Y),
            Galois' X W P R xord word f g->Galois' Y Z Q S yord zord h i->
            Galois' (orthoprod X Y)(orthoprod W Z )(compprop X Y P Q)(compprop W Z R S)(compord X Y xord yord)
            (compord W Z word zord)(compfunc W X Y Z f h)(compfunc X W Z Y g i).
        Proof.
            unfold compord. unfold compfunc. unfold compprop.
            intros. unfold Galois'. unfold posubset. unfold reflex'.
            unfold antisym'. unfold transit'. split. split; intros. 
            split. apply H. apply H1. apply H0. apply H1.
            split; intros. 
            rewrite product_terms. rewrite product_terms with (p:=x). 
            destruct H3. destruct H4. destruct H. destruct H. 
            apply H8 in H3. apply H3 in H4.
            destruct H0. destruct H0. apply H10 in H5. apply H5 in H6.
            rewrite H4. rewrite H6. reflexivity. apply H1. apply H2.
            apply H1. apply H2.
            split. apply H with (y:=(fst X Y y)). 
            apply H1. apply H2. apply H3. apply H4. apply H5. 
            apply H0 with (y:=(snd X Y y)). 
            apply H1. apply H2. apply H3. apply H4. apply H5.
            split. split; intros.
            split. apply H. apply H1. apply H0. apply H1.
            split; intros.
            rewrite product_terms. rewrite product_terms with (p:=x).
            destruct H3. destruct H4. 
            destruct H. destruct H7. destruct H7. apply H9 in H3. apply H3 in H4.
            destruct H0. destruct H10. destruct H10. apply H12 in H5. apply H5 in H6.
            rewrite H4. rewrite H6. reflexivity.
            apply H1. apply H2. apply H1. apply H2.
            split; [apply H with (y:=fst W Z y)|apply H0 with (y:=snd W Z y)];
            try apply H1; try apply H2; try apply H3; try apply H4; try apply H5.
            intros. split; intros. split.
            simpl. apply H. apply f. apply (fst X Y x). apply H1.
            simpl. apply H0. apply h. apply (snd X Y x). apply H1.
            split; intros. split.
            simpl. apply H. apply g. apply (fst W Z y). apply H1.
            simpl. apply H0. apply i. apply (snd W Z y). apply H1.
            split; intros; split; simpl; simpl in H3; destruct H3.
            apply H. apply H1. apply H2. apply H3.
            apply H0. apply H1. apply H2. apply H4.
            apply H. apply H1. apply H2. apply H3.
            apply H0. apply H1. apply H2. apply H4.
            Qed.

        Definition pool_minimum (A B C D: Type)(g:C->A)(i:D->(A->B))(aord:A->A->Prop)
                        (xord: (A->B)->(A->B)->Prop)(S:C->Prop)(T:D->Prop):Prop:=
            forall (c1 c2: C)(d1 d2: D), S c1->S c2->T d1->T d2->i(d1) (g(c1)) =i(d2) (g(c2))
            ->(aord (g c1) (g c2)/\xord (i d1) (i d2))\/(aord (g c2) (g c1)/\xord (i d2) (i d1)).

        Definition orderability (A B C D: Type)(g:C->A)(i:D->(A->B))(aord:A->A->Prop)
                        (xord: (A->B)->(A->B)->Prop)(P:A->Prop)(Q: (A->B)->Prop)(R:B->Prop)
                        (S:C->Prop)(T:D->Prop):Prop:=
            exists (funct: B->orthoprod A (A->B)),
            forall (b:B) (c: C)(d:D), (R b->P (fst A (A->B) (funct b))/\ Q (snd A (A->B) (funct b))
            /\(snd A (A->B) (funct b)) (fst A (A->B) (funct b))=b)/\
            (S c->T d->
            aord (fst A (A->B) (funct (i d (g c))))(g c)/\xord(snd A (A->B) (funct (i d (g c)))) (i d))
            /\(R b->S c->T d-> aord (fst A (A->B) (funct b))(g c)->
            xord (snd A (A->B) (funct b))(i d)->
             aord  (fst A (A->B) (funct b))(fst A (A->B) (funct (i d (g c))))/\
             xord (snd A (A->B) (funct b))(snd A (A->B) (funct (i d (g c)))) ).

        Definition depfunc (A B C D: Type)(g:C->A)(i:D->(A->B)) (p:orthoprod C D): B:=
            i(snd C D p)(g(fst C D p)). 

        Definition depord (A B:Type)(aord:A->A->Prop)(xord:(A->B)->(A->B)->Prop)(func: B->orthoprod A (A->B))(b1 b2: B):Prop:=
            aord (fst A (A->B) (func b1)) (fst A (A->B) (func b2))/\xord (snd A (A->B) (func b1))(snd A (A->B) (func b2)).


        Theorem dependent_product: forall (A B C D: Type)(P:A->Prop)(Q:(A->B)->Prop)(R:B->Prop)
                        (S:C->Prop)(T:D->Prop)(aord:A->A->Prop)(xord:(A->B)->(A->B)->Prop)
                        (cord:C->C->Prop)(dord:D->D->Prop)(f:A->C)(g:C->A)(h:(A->B)->D)(i:D->(A->B)),
            Galois' A C P S aord cord f g->Galois' (A->B) D Q T xord dord h i->
            (forall (a:A)(x:A->B), P a->Q x-> R (x a))->
            orderability A B C D g i aord xord P Q R S T->
            exists (func: B->orthoprod A (A->B)), Galois' B (orthoprod C D) R (compprop C D S T) 
            (depord A B aord xord func)(compord C D cord dord)
            (composite func (compfunc C A (A->B) D f h)) (depfunc A B C D g i).
        Proof.
            unfold pool_minimum. unfold orderability. unfold Galois'. unfold posubset. 
            unfold reflex'. unfold antisym'. unfold transit'. unfold depord. unfold depfunc.
            unfold compord. unfold compprop. unfold compfunc. 
            intros. destruct H2. exists x. split. split.
            intros. split; [apply H|apply H0]; apply H2; try assumption;
            try apply f; try apply h; try apply x; assumption.
            split. intros. 
            assert (eqn: fst A (A->B) (x x0)=fst A (A->B) (x y) ).
            apply H; try apply H2; try apply f; try apply h; try apply x;
            try assumption. apply H5. apply H6.
            assert (eqn': snd A (A->B) (x x0)=snd A (A->B) (x y)).
            apply H0; try apply H2; try apply f; try apply h; try apply x;
            try assumption. apply H5. apply H6.
            apply H2 in H3. destruct H3. destruct H7. rewrite<-H8.
            apply H2 in H4. destruct H4. destruct H9. rewrite<-H10.
            rewrite eqn. rewrite eqn'. reflexivity.
            apply f. apply x. assumption. apply h. apply x. assumption.
            apply f. apply x. assumption. apply h. apply x. assumption.
            intros. split. 
            apply H with (y:=(fst A (A -> B) (x y))); try apply H2; 
            try apply h; try apply f; try apply x;
            try assumption. apply H6. apply H7.
            apply H0 with (y:=(snd A (A->B) (x y))); try apply H2; 
            try apply h; try apply f; try apply x;
            try assumption. apply H6. apply H7.
            split. split; intros.
            split. apply H. apply H3. apply H0. apply H3.
            split; intros.
            assert (eqn: (fst C D x0)=(fst C D y)). apply H.
            apply H3. apply H4. apply H5. apply H6.
            assert (eqn': (snd C D x0)=(snd C D y)). apply H0.
            apply H3. apply H4. apply H5. apply H6.
            rewrite product_terms. rewrite product_terms with (p:=x0).
            rewrite eqn. rewrite eqn'. reflexivity.
            split. apply H with (y:=(fst C D y)). 
            apply H3. apply H4. apply H5. apply H6. apply H7.
            apply H0 with (y:=(snd C D y)).
            apply H3. apply H4. apply H5. apply H6. apply H7.
            intros. split; intros. split; simpl. 
            apply H. apply f. apply x. apply x0. apply H2.
            apply f. apply x. assumption. apply h. apply x. assumption. assumption.
            apply H0. apply h. apply x. apply x0. apply H2. 
            apply f. apply x. assumption. apply h. apply x. assumption. assumption.
            split; intros.
            apply H1. apply H. apply x. apply x0. apply H3.
            apply H0. apply x. apply x0. apply H3.
            split; intros. split; simpl.
            apply H. apply H2.
            apply f. apply x. assumption. apply h. apply x. assumption. apply H3. apply H4.
            apply H with (y:=(fst A (A -> B) (x (i (snd C D y) (g (fst C D y)))))).
            apply H2.  apply f. apply x. assumption. apply h. apply x. assumption. assumption.
            apply H2.  apply f. apply x. assumption. apply h. apply x. assumption. 
            apply H1. apply H. apply x. assumption. apply H4.
            apply H0. apply x. assumption. apply H4.
            apply H. apply x. assumption. apply H4.
            apply H5. apply H2; try apply H4. assumption.
            apply H0. apply H2.  
            apply f. apply x. assumption. apply h. apply x. assumption.
            assumption. apply H4. 
            apply H0 with (y:=(snd A (A -> B) (x (i (snd C D y) (g (fst C D y)))))).
            apply H2. apply f. apply x. assumption. apply h. apply x. assumption.
            assumption. apply H2. apply f. apply x. assumption. apply h. apply x. assumption.
            apply H1. apply H. apply x. assumption. apply H4.
            apply H0. apply x. assumption. apply H4.
            apply H0. apply x. assumption. apply H4.
            apply H5. apply H2; try apply H4. assumption.
            split; simpl in H5; destruct H5;
            apply H in H5; apply H0 in H6.
            apply H2. assumption. apply H4. apply H4. assumption. assumption.
            apply H2; try assumption; [apply f|apply h]; apply x; assumption.
            apply H4.
            apply H2; try assumption; [apply f|apply h]; apply x; assumption.
            apply H2; try assumption; [apply f|apply h]; apply x; assumption.
            apply H4. apply H4.
            apply H2; try assumption; [apply f|apply h]; apply x; assumption.
            apply H4.
            apply H2. assumption. apply H4. apply H4. assumption. assumption.
            apply H2; try assumption; [apply f|apply h]; apply x; assumption.
            apply H4.
            apply H2; try assumption; [apply f|apply h]; apply x; assumption.
            apply H2; try assumption; [apply f|apply h]; apply x; assumption.
            apply H4. apply H4.
            apply H2; try assumption; [apply f|apply h]; apply x; assumption.
            apply H4.
            Qed.

            



            

            




    


        




            
            

            




 










    