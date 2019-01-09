Require Import OrderedType OrderedTypeEx OrderedTypeAlt DecidableType DecidableTypeEx.
Require Import RelationClasses FunInd.
From bcv Require Import vmtype dvm ovm.
Require bcv.heritage.

Module Offensive_correcte (H:heritage.Herit).

  Module D:= D(H).
  Module O:= O(H).

  (** Calcul de la valeur offensive d'une valeur défensive: on enlève
  le tag de type,et on met zéro là où il n'y a pas de valeur, de toute
  façon si le bcv est correct et accepte une applet, ces valeurs
  n'apparaitront jamais. *)
  Definition d2o (v:DefVal.DVal): OffVal.Val :=
    match v with
      | DefVal.Vint i => i
      | DefVal.Vref (_,i) => i
      | DefVal.Vrefnull => 0
      | DefVal.Error => 0
      | DefVal.NonInit => 0
    end.

  (** * Les fonctions d'offensivisation: on applique d2o partout. *)

  Definition offensive_regs rgs: O.Registers := Dico.map d2o rgs.

  Definition offensive_stack st: O.Stack := List.map d2o st.

  Definition offensive_heap hp: O.Heap :=
    Dico.map (fun obj =>
                {| O.objclass:= obj.(D.objclass) ; O.objfields := Dico.map d2o (obj.(D.objfields)) |}) hp.

   Definition offensive_frame (f:D.Frame) : O.Frame :=
     {| O.mdef := f.(D.mdef);
        O.regs := offensive_regs (f.(D.regs));
        O.stack := offensive_stack (f.(D.stack));
        O.pc := f.(D.pc) |}.

 Definition offensive_state (s:D.State) : O.State :=
    {| O.frame := offensive_frame (s.(D.frame));
       O.framestack := nil;
       O.heap := offensive_heap s.(D.heap) |}.


  Definition offensive_opt_state (s:option D.State) : option O.State :=
    match s with
      | None => None
      | Some x => Some (offensive_state x)
    end.


  Lemma pc_ok: forall s,  (s.(D.frame)).(D.pc) = (O.frame (offensive_state s)).(O.pc).
    destruct s;simpl;reflexivity.
  Qed.

  Lemma mdef_ok: forall s, D.mdef(s.(D.frame)) = O.mdef(O.frame(offensive_state s)).
  Proof.
    destruct s;simpl;reflexivity.
  Qed.

  Lemma regs_ok: forall s, offensive_regs (D.regs(D.frame(s))) = O.regs(O.frame(offensive_state s)).
  Proof.
    destruct s;cbn; reflexivity.
  Qed.

  Lemma stack_ok: forall s, offensive_stack (D.stack(s.(D.frame))) = O.stack(O.frame(offensive_state s)).
  Proof.
    destruct s;simpl.
    induction (D.stack frame).
    - easy.
    - apply map_cons.
  Qed.

  Lemma heap_ok: forall s, offensive_heap (D.heap(s)) = O.heap(offensive_state s).
  Proof.
    destruct s;cbn; reflexivity.
  Qed.

  Lemma frame_ok: forall s, offensive_frame (s.(D.frame)) = (O.frame (offensive_state s)).
  Proof.
    destruct s;cbn; reflexivity.
  Qed.

  Definition d2o_opt := option_map d2o.


  Add Morphism offensive_regs with signature Dico.Equal ==> Dico.Equal as off_regs_m.
  Proof.
    intros rgs1 rgs2 H.
    unfold offensive_regs.
    apply Dicomore.map_m with (x:= d2o) (y:= d2o) in H.
    - assumption.
    - reflexivity.
  Qed.


  Lemma find_offensive_ok : forall rgs ridx, 
                              Dico.find ridx (offensive_regs rgs) 
                              = d2o_opt (Dico.find ridx rgs).
  Proof.
    intros rgs.
    induction rgs using  Dicomore.map_induction_bis;simpl;intros.
    - rewrite <- H.
      apply IHrgs1.
    - vm_compute.
      reflexivity. 
    - unfold offensive_regs.
      rewrite Dicomore.map_o.    
      reflexivity.
  Qed.
  Import D.

  (** Diagramme de commutation entre D et O. *)
  Lemma offensive_ok : 
    forall (s s':D.State) (os os' os'':O.State),
      offensive_state s = os ->
      offensive_state s' = os' ->
      D.exec_step s = Some s' ->
      O.exec_step os = Some os'' -> 
      O.state_eq os' os''.
  Proof.


    intros s s' os os' os'' Hos Hos' Hd Ho.
    unfold O.exec_step in Ho; cbn in Ho.
    subst os.
    rewrite <- pc_ok in Ho.
    rewrite <- mdef_ok in Ho.
    rewrite <- regs_ok in Ho.
    rewrite <- stack_ok in Ho.
    rewrite <- heap_ok in Ho.

    functional induction (D.exec_step s)
    ; try discriminate Hd
    ; rewrite e in Ho
    ; try rewrite find_offensive_ok in Ho
    ; try rewrite e1 in Ho
    ; inversion Hd ; clear Hd ; subst s'
    ; unfold offensive_state in Hos'; cbn in Hos'; subst os'
    ; cbn in Ho; inversion Ho; clear Ho; rename H0 into Ho
    ; try subst os'';cbn
    ; try (apply O.state_eq_C
           ; cbn
           ; [apply O.frame_eq_C| |apply O.heap_eq_C]
           ;cbn
           ;try apply Dicomore.add_map
           ;easy).
    (* TODO here *)

End Offensive_correcte.
