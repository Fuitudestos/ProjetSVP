From bcv Require Import heritage vmtype vmdefinition  LibHypsNaming.
Require Import List FunInd.
Import ListNotations.

(** * Valeurs de la machine abstraite

   On abstrait les défintions ci-dessus: on enlève les valeurs et les adresses
   mémoire et on les remplace par les types. *)

Module AbsVal <: VMVal.
  Definition Val := VMType.
  
  (** Calcul du type d'une valeur défensive. *)
  Definition v2t (v:Val): VMType := v.

End AbsVal.


Module A (Import H:Herit).
  Module Abs := VMDefinition(AbsVal)(H).
  Include Abs.

  Ltac rename_avm h th := fail.

  (* Hypothesis renaming stuff from other files + current file.
     DO NOT REDEFINE IN THIS FILE. Redefine rename_avm instead. *)
  Ltac rename_hyp h th ::=
    match th with
    | _ => (rename_avm h th)
    | _ => (Abs.rename_vmdef h th)
    | _ => (LibHypsNaming.rename_hyp_neg h th)
    end.


(** * Exécution de la machine défensive.
   Pas de vérif de overflow. pas de nb négatifs. *)
  Definition exec_step (s:State): list (option State) :=
    let frm:Frame := s.(frame) in
    let pc: pc_idx := frm.(pc) in
    let instr_opt := Dico.find pc (frm.(mdef).(instrs)) in
    match instr_opt with
    | None => [None]
    | Some instr =>
      match instr with
      | ret => [Some s]
      | Iconst i =>
        [Some {| framestack := s.(framestack); heap := s.(heap);
                frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                            pc:= pc + 1;
                            stack:= Tint :: s.(frame).(stack)
                         |}
             |}]
      | Iadd =>
        match s.(frame).(stack) with
        | Tint :: Tint :: stack' =>
          [Some  {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef); regs:= s.(frame).(regs);
                              pc:= pc + 1;
                              stack:= Tint :: stack'
                           |}
               |} ]
         | nil | _ :: nil => [None]
         | _ :: _ => [None]
        end

      | Iload ridx =>
        match Dico.find ridx (s.(frame).(regs)) with
        | Some Tint =>
          [Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef); regs:= s.(frame).(regs);
                              pc:= pc + 1;
                              stack:= Tint :: s.(frame).(stack)
                           |}
               |}]
        | Some _ (** Invalid register content *)
        | None => [None] (** Bad register number *)
        end

      | Rload clid ridx =>
        match Dico.find ridx (s.(frame).(regs)) with
        | Some (Tref r) =>
          [Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              pc:= pc + 1;
                              stack:= Tref r :: s.(frame).(stack)
                           |}
               |}]
        | Some _ (** Invalid register content *)
        | None => [None] (** Bad register number *)
        end

      | Istore ridx =>
        match s.(frame).(stack) with
        | Tint :: stack' =>
          [Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ;
                              regs:= Dico.add ridx Tint (s.(frame).(regs));
                              pc:= pc + 1;
                              stack:= stack'
                           |}
               |}]
        | nil
        | _ => [None] (** Stack underflow *)
        end

      | Rstore clid ridx =>
        match s.(frame).(stack) with
        | Tref r :: stack' =>
          [Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ;
                              regs:= Dico.add ridx (Tref r) (s.(frame).(regs));
                              pc:= pc + 1;
                              stack:= stack'
                           |}
               |}]
        | nil => [None] (** Stack underflow *)
        | _ => [None]
        end

      | Iifle jmp => (** ifeqe *)
        match s.(frame).(stack) with
        | Tint :: stack' => (** = 0  --> jump *)
          [Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              pc:= jmp;
                              stack:= stack'
                           |}
                |}
          ; Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              pc:= pc+1;
                              stack:= stack'
                           |}
                 |}]
        | _ :: _ | nil => [None] (** Stack underflow *)
        end

      | Goto jmp =>
        [Some {| framestack := s.(framestack); heap := s.(heap);
                frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                            stack:= s.(frame).(stack);
                            pc:= jmp
                         |}
             |}]

      | Getfield cl namefld typ =>
        match s.(frame).(stack) with
        | Tint :: stack' =>
          [Some {| framestack := s.(framestack); heap := s.(heap);
                   frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                               pc:= pc+1;
                               stack:= typ :: stack'
                            |}
                |}]
        | nil => [None] (** Stack underflow *)
        | _ => [None]
        end

      | Putfield cl namefld typ =>
        match s.(frame).(stack) with
        | Tint :: t :: stack' =>
          [Some {| framestack := s.(framestack);
                   heap := s.(heap);
                   frame := {| mdef:=s.(frame).(mdef) ;
                               regs:= s.(frame).(regs);
                               pc:= pc+1;
                               stack:= stack'
                            |}
                |}]
        | nil | _ :: nil => [None] (** Stack underflow *)
        | _ :: _ => [None]
        end

      | New clid =>
          [Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              stack:= Tref clid :: s.(frame).(stack);
                              pc:= pc+1
                           |} 
               |}]

      end
    end.

(** * Tests *)

  Notation "k --> i , d" := (Dico.add k i d) (at level 55, right associativity).

  Definition prog:MethodDef := 
    {| instrs := (0 --> Iload 1 ,
                  1 --> Istore 2 ,
                  2 --> ret ,
                  Dico.empty ) ;
       argstype := Tint :: Tint:: nil;
       restype := Tint |}.

  Definition startstate:State := 
    {| 
      framestack := nil;
      heap:= Dico.empty ;
      frame := {|
        mdef:= prog ; 
        regs:= (0 --> Tint , 1 --> Tint, Dico.empty);
        pc:= 0;
        stack:= nil
        |}
      |}.

  Fixpoint exec_n (s : State) (n:nat) {struct n}: list (option State) :=
    match n with
      | 0 => [ Some s ]
      | S n' =>
        let ls' := exec_step s in
          (fix exec_l_n (ls:list (option State)) {struct ls}: list (option State) :=
          match ls with
            | nil => nil
            | None :: ls' => None :: exec_l_n ls'
            | Some s' :: ls' => List.app (exec_n s' n') (exec_l_n ls')
          end) ls'
    end.

  Eval simpl in exec_n startstate 1.
  Eval simpl in exec_n startstate 2.
  Eval simpl in exec_n startstate 5.

  Functional Scheme exec_step_ind := Induction for exec_step Sort Prop.

  Lemma essai : forall s x,
    exec_step s = [ Some x ] -> 
    x.(framestack) = s.(framestack).
  Proof.
    intros s.
    functional induction exec_step s;intros ;simpl;
      try solve [discriminate | inversion H; subst;simpl;reflexivity] .
  Qed.

  Lemma essai2 : forall s x y,
    exec_step s = [ Some x ; Some y] -> 
    x.(framestack) = s.(framestack).
  Proof.
    intros s.
    functional induction exec_step s;intros ;simpl;
      try solve [discriminate | inversion H; subst;simpl;reflexivity] .
  Qed.

End A.

