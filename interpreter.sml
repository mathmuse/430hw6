use "printAST.sml";

open HashTable;

val hashFn = HashString.hashString;
val cmpFn = (op =);
exception MissingId;
val initSize = 20;
val debug = true;
val verbose = false;

fun getTag() =
   ref 0;

fun 
   getBinString BOP_PLUS = "+"
 | getBinString BOP_MINUS = "-"
 | getBinString BOP_TIMES = "*"
 | getBinString BOP_DIVIDE = "/"
 | getBinString BOP_MOD = "%"
 | getBinString BOP_EQ = "=="
 | getBinString BOP_NE = "!="
 | getBinString BOP_LT = "<"
 | getBinString BOP_GT = ">"
 | getBinString BOP_LE = "<="
 | getBinString BOP_GE = ">="
 | getBinString BOP_AND = "&&"
 | getBinString BOP_OR = "||"
 | getBinString BOP_COMMA = ","
;

fun 
   getUnString UOP_NOT = "!"
 | getUnString UOP_TYPEOF = "typeof"
 | getUnString UOP_MINUS = "-"
;

fun getBool bl = if bl then EXP_TRUE else EXP_FALSE;

fun 
   getBoolVal EXP_TRUE = true
 | getBoolVal EXP_FALSE = false
 | getBoolVal _  = error "trying to get boolval of non bool"
;

fun isBool EXP_FALSE = true
  | isBool EXP_TRUE = true
  | isBool n = false
;

fun typeError opr req fnd = 
   error ("operator '" ^ opr ^ "' requires " ^ req ^ ", found " ^ fnd)
;

fun binNumCheck a b = 
   case a of 
      EXP_NUM _ => 
         (case b of 
            EXP_NUM _ => true
          | _ => false)
    | _ => false     
;

fun binStringCheck a b =
   case a of
      EXP_STRING _ =>
         (case b of
            EXP_STRING _ => true
          | _ => false)
     | _ => false 

fun binBoolCheck a b = 
   case isBool a of
      true  =>
         (case isBool b of
            true => true
          | false => false)
     | false => false 
; 

fun binUndefinedCheck a b = 
   case a of
      EXP_UNDEFINED  =>
         (case b of
            EXP_UNDEFINED => true
          | _ => false)
     | _ => false 
; 
fun binFunctionCheck a b = 
   case a of
      EXP_CLOSURE _  =>
         (case b of
            EXP_CLOSURE _ => true
          | _ => false)
     | _ => false 
; 

fun binSameCheck a b = 
   binBoolCheck a b orelse 
   binStringCheck a b orelse 
   binNumCheck a b orelse
   binUndefinedCheck a b orelse
   binFunctionCheck a b
;

fun 
   unBoolCheck EXP_TRUE = true
 | unBoolCheck EXP_FALSE = true
 | unBoolCheck _ = false
;

fun
   unNumCheck (EXP_NUM _) = true
 | unNumCheck _ = false
;

fun doNot a = getBool ( not (getBoolVal a));

val numType = "number";
val boolType = "boolean";
val undefinedType = "undefined";
val stringType = "string";
val closureType = "function";
val objectType = "object";

fun 
   doTypeof (EXP_NUM _) = EXP_STRING numType
 | doTypeof EXP_TRUE = EXP_STRING boolType
 | doTypeof EXP_FALSE = EXP_STRING boolType
 | doTypeof EXP_UNDEFINED = EXP_STRING undefinedType
 | doTypeof (EXP_STRING _) = EXP_STRING stringType
 | doTypeof (EXP_CLOSURE _) = EXP_STRING closureType
 | doTypeof (EXP_ACTUALOBJECT _) = EXP_STRING objectType
 | doTypeof (EXP_ID _) = EXP_STRING "id"
 | doTypeof _ = error "unknown type1!"
;

fun 
   getType (EXP_NUM _) = numType
 | getType EXP_TRUE = boolType
 | getType EXP_FALSE = boolType
 | getType EXP_UNDEFINED = undefinedType
 | getType (EXP_STRING _) = stringType
 | getType (EXP_CLOSURE _) = closureType
 | getType (EXP_ACTUALOBJECT _) = objectType
 | getType _ = error "unknown type2!"
;

fun doMinus (EXP_NUM n) = EXP_NUM (~n)
  | doMinus _ = error "bad minus"
;

fun
   doNumBinary BOP_PLUS (EXP_NUM a) (EXP_NUM b) = EXP_NUM (a+b)
 | doNumBinary BOP_MINUS (EXP_NUM a) (EXP_NUM b) = EXP_NUM (a-b)
 | doNumBinary BOP_TIMES (EXP_NUM a) (EXP_NUM b) = EXP_NUM (a*b)
 | doNumBinary BOP_DIVIDE (EXP_NUM a) (EXP_NUM b) = EXP_NUM (Int.div(a,b))
 | doNumBinary BOP_MOD (EXP_NUM a) (EXP_NUM b) = EXP_NUM (Int.mod(a,b))
 | doNumBinary _ _ _ = error "not a num binary"
;

fun
   doRelBinary BOP_LT (EXP_NUM a) (EXP_NUM b) = getBool (a < b)
 | doRelBinary BOP_LE (EXP_NUM a) (EXP_NUM b) = getBool (a <= b)
 | doRelBinary BOP_GT (EXP_NUM a) (EXP_NUM b) = getBool (a > b) 
 | doRelBinary BOP_GE (EXP_NUM a) (EXP_NUM b) = getBool (a >= b) 
 | doRelBinary _ _ _ = error "not a eq binary"
;

fun 
   doEqBinary BOP_EQ (EXP_NUM a) (EXP_NUM b) = getBool (a = b)
 | doEqBinary BOP_NE (EXP_NUM a) (EXP_NUM b) = getBool (a <> b)
 | doEqBinary BOP_EQ (EXP_CLOSURE {body=_,parms=_,env=_,r=a}) (EXP_CLOSURE {body=_,parms=_,env=_,r=b}) = getBool (a = b)
 | doEqBinary BOP_NE (EXP_CLOSURE {body=_,parms=_,env=_,r=a}) (EXP_CLOSURE {body=_,parms=_,env=_,r=b}) = getBool (a <> b)
 | doEqBinary _ _ _ = error "not a bool binary"
;

fun
   doStringBinary BOP_PLUS (EXP_STRING a) (EXP_STRING b) = EXP_STRING (a ^ b) 
 | doStringBinary _ _ _ = error "not a string binary"
;

fun println str = 
   print (str ^ "\n") 
;

fun newTable() = mkTable (hashFn, cmpFn) (initSize, MissingId);

fun newEnvironment prev = 
   ENV {
      st = mkTable (hashFn, cmpFn) (initSize, MissingId),
      prev = SOME prev 
   } 
;
fun newBaseEnvironment () = 
   ENV {
      st = mkTable (hashFn, cmpFn) (initSize, MissingId),
      prev = NONE 
   } 
;

fun printObj st = 
   let val pairs = listItemsi st
       fun printKey (a,b) = 
         ("   " ^ a ^ ": " ^ (if verbose then printExpression b else printExpr b) ^ " ")
   in
      "{ " ^ foldl (op ^) ""  (List.map printKey pairs) ^ " }"
   end 
   

and printState (st : (string, expression) hash_table) = 
   let val pairs = listItemsi st 
       fun printKey (a,b) = 
         print ("|   " ^ a ^ ": " ^ (if verbose then printExpression b else printExpr b) ^ "\n\n")
 
   in
      List.map printKey pairs
   end
and 
   printEnv2 (ENV {st=st, prev=(SOME nextEnv)}) = 
      (print "|  Env:\n"; printState st; print "|\n"; printEnv2 nextEnv)
 | printEnv2 (ENV {st=st, prev=NONE}) = 
      (print "|  Env:\n"; printState st; print "|\n")
and printEnv env = 
   if debug then
      (print "\nv---------------v\n"; printEnv2 env; print "^---------------^\n")
   else ()
and printExpr exp = 
   let 
      val str = case exp of 
         EXP_NUM n => String.map (fn x => case x of #"~" => #"-" | n => n) (Int.toString n)
       | EXP_STRING n => n
       | EXP_ID n => n
       | EXP_TRUE => "true"
       | EXP_FALSE => "false"
       | EXP_UNDEFINED => "undefined"
       | EXP_BINARY _ => error "bin print"
       | EXP_UNARY _ => error "un print"
       | EXP_COND _ => error "cond print"
       | EXP_ASSIGN _ => error "assign print"
       | EXP_VAR _ => error "var print"
       | EXP_VARASSIGN _ => error "varassign print"
       | EXP_CALL _ => error "call print"
       | EXP_ARG _ => "argprint"
       | EXP_FUN n => "function"
       | EXP_ANON n => "function"
       | EXP_CLOSURE n => "function"
       | EXP_NAMEDCLOSURE n => "namedclosure" 
       | EXP_NONE => "none print"
       | EXP_THIS =>  "this"
       | EXP_OBJECT _ => "object print"
       | EXP_OBJECTASSIGN _ => "objectassign print"
       | EXP_NEW _ => error "new print"
       | EXP_IDS _ => "ids-print"
       | EXP_DOTID _ => error "dotid print"
       | EXP_ACTUALOBJECT {st=st} => (printObj st)
   in
      str
   end
;
  

fun getState (ENV {st=st, prev = prev}) = 
   st 
;

fun setPrev (ENV {st=st, prev = n}) prev1 = 
   ENV {st=st, prev= (SOME prev1)}
;

fun
   hasKey tbl id = 
      case find tbl id of
         NONE => false
       | (SOME x) => true
;

fun 
   insertVal id ((EXP_ID h) :: t) v st = 
      let val found = find st id in
         case found of 
            SOME (EXP_ACTUALOBJECT {st=newst}) => insertVal h t v newst 
          | _ => error "sad object"
      end
 | insertVal id [] v st = 
      insert st (id, v) 
;

fun 
   setVar id ids v (ENV {st=st, prev = (SOME prev)}) = 
      if hasKey st id  
      then 
         insertVal id ids v st
      else setVar id ids v prev
 | setVar id ids v (ENV {st=st, prev = NONE}) = 
         insertVal id ids v st
;

fun
   findVal id ((EXP_ID h)::t) st =
      let val found = find st id in 
         case found of
            SOME (EXP_ACTUALOBJECT {st=newst}) => findVal h t newst 
          | _ => error "more sad object"
      end
 | findVal id [] st =
      let val found = find st id in
         case found of 
            SOME n => n
          | NONE => EXP_UNDEFINED
      end
;

fun 
   getVar id ids (ENV {st=st, prev = (SOME prev)}) = ( 
      case find st id of
         SOME n => findVal id ids st
       | NONE => getVar id ids prev
   )
 | getVar id ids (ENV {st=st, prev = NONE}) = (
      case find st id of
         SOME n => findVal id ids st
       | NONE => EXP_UNDEFINED
   )
;

fun inReturn (ENV {st=st, prev=prev}) = 
  case prev of
      SOME _ => true
    | NONE => false
;

fun interpret fname =
   let
      val ast = parse fname
   in
      intProgram ast
   end

and intProgram (PROGRAM {elems=elems}) = 
   let
      val st = newBaseEnvironment ()
   in
      intSubProgram elems st
   end

and
   blockPass (h::t) st =
      let val (ret1, st1) = intSourceElement h st in 
         case ret1 of 
            EXP_NONE => blockPass t st1
          | n => (ret1, st1)
      end
 | blockPass [] st = (EXP_NONE, st)

and 
   intSubProgram ls st = 
      let val (tk1, st1) = firstPass ls st 
          val (tk2, st2) = secondPass ls st1
      in
         thirdPass ls st2
      end

and
   firstPass (h::t) st =
      (case h of 
         STMT {stmt=(ST_VAR n)} => 
            let val (ret1, st1) = intVarStatementFirst (ST_VAR n) st in 
               case ret1 of 
                  EXP_NONE => firstPass t st1
                | n => (ret1, st1)
            end
       | STMT {stmt = (ST_ITER {whil=whil, block=(ST_BLOCK ls1)})} =>
            let val st1 = st
                val (ret2, st2) = firstPass ls1 st1
            in
              case ret2 of 
                  EXP_NONE => firstPass t st2
                | n => (ret2, st2) 
            end
       | STMT {stmt = (ST_IF {iff=iff, thn=(ST_BLOCK ls1)})} =>
            let val (ret1, st1) = firstPass ls1 st
            in
              case ret1 of 
                  EXP_NONE => firstPass t st1
                | n => (ret1, st1) 
            end
       | STMT {stmt = (ST_IFELSE {iff=iff, thn=(ST_BLOCK ls1), el=(ST_BLOCK ls2)})} =>
            let val (ret1, st1) = firstPass ls1 st
                val (ret2, st2) = firstPass ls2 st1
            in
              case ret2 of 
                  EXP_NONE => firstPass t st2
                | n => (ret2, st2) 
            end
       | _ => firstPass t st)
 | firstPass [] st = (EXP_UNDEFINED, st)

and
   secondPass (h::t) st =
      (case h of 
         FUNC _ => 
            let val (ret1, st1) = intSourceElement h st in 
               case ret1 of 
                  EXP_NONE => secondPass t st1
                | n => (ret1, st1)
            end
       | _ => secondPass t st)
 | secondPass [] st = (EXP_UNDEFINED, st)

and
   thirdPass (h::t) st =
      (case h of 
         (*STMT {stmt=(ST_VAR _)} => thirdPass t st*)
        STMT _ => 
            let val (ret1, st1) = intSourceElement h st in 
               case ret1 of 
                  EXP_NONE => thirdPass t st1
                | n => (ret1, st1)
            end
       | _ => thirdPass t st)
 | thirdPass [] st = (EXP_UNDEFINED, st)

and 
   intSourceElement (STMT {stmt=stmt}) st = intStatement stmt st
 | intSourceElement (FUNC {id=id, parms=parms, body=body}) st = 
      intFunction id parms body st

and intFunction (EXP_ID id) parms body st =  
   let val closure = (EXP_CLOSURE {body=body, parms=(idToString parms), env=st, r=(getTag())}) in
      (setVar id [] closure st; (EXP_NONE, st))
   end

and 
   intStatement (ST_EXP {exp=exp}) st =
      let val (v, st1) = intExpression exp st
      in
         (EXP_NONE, st1)  
      end 
 | intStatement (ST_PRINT exp) st = 
      (EXP_NONE, intPrint exp st)
 | intStatement (ST_BLOCK ls) st = 
      intBlock ls st
 | intStatement (ST_IF {iff=iff, thn=thn}) st = 
      intIf (ST_IF {iff=iff, thn=thn}) st
 | intStatement (ST_IFELSE {iff=iff, thn=thn, el=el}) st = 
      intIfElse (ST_IFELSE {iff=iff, thn=thn, el=el}) st
 | intStatement (ST_ITER {whil=whil, block=block}) st = 
      intIter whil block st
 | intStatement (ST_VAR (h::t)) st = 
      let val (ast1, st1) = intExpression h st in
         intStatement (ST_VAR t) st1
      end
 | intStatement (ST_VAR []) st = 
      (EXP_NONE, st)
 | intStatement (ST_RETURN) st = intReturn st
 | intStatement (ST_RETURNVAL expr) st = intReturnVal expr st

and
   intVarStatementFirst (ST_VAR (h::t)) st = 
      let val (ast1, st1) = intVarFirst h st in
         intStatement (ST_VAR t) st1
      end
 | intVarStatementFirst (ST_VAR []) st = 
      (EXP_NONE, st)
and
   intVarFirst (EXP_VAR {id=(EXP_ID id)}) st = 
      if hasKey (getState st) id then
         (EXP_ID id, st)
      else
         (insert (getState st) (id, EXP_UNDEFINED); (EXP_ID id, st)) 
 | intVarFirst (EXP_VARASSIGN {id=id, assign=assign}) st = 
      intVarFirst (EXP_VAR {id=id}) st

and intReturn st = 
   if inReturn st then
      (EXP_UNDEFINED, st)
   else
      error "return statements are only valid inside functions"
and intReturnVal expr st = 
   if inReturn st then
      let val (v1, st1) = intExpression expr st in
         (v1, st1)
      end
   else    
      error "return statements are only valid inside functions"

and
   intIter whil block st = 
      let val (gd, st1) = intExpression whil st
      in
         if unBoolCheck gd
         then 
            if getBoolVal gd
            then
               let val (ret2, st2) = intStatement block st1
               in
                  case ret2 of 
                     EXP_NONE => intIter whil block st2
                   | _ => (ret2, st2) 
               end
            else (EXP_NONE, st1)
         else error ("boolean guard required for 'while' statement, found " ^ (getType gd))
      end

and intIf (ST_IF {iff=iff, thn=thn}) st = 
   let val (gd, st1) = intExpression iff st
   in
      if unBoolCheck gd
      then 
         if getBoolVal gd
         then
            let val (v, st2) = intStatement thn st1 in
               (v, st2)
            end
         else (EXP_NONE, st1)
      else error ("boolean guard required for 'if' statement, found " ^ (getType gd))
   end

and intIfElse (ST_IFELSE {iff=iff, thn=thn, el=el}) st = 
   let val (gd, st1) = intExpression iff st
   in
      if unBoolCheck gd
      then if getBoolVal gd
         then
            intStatement thn st1
         else
            intStatement el st1
      else error ("boolean guard required for 'if' statement, found " ^ (getType gd))
   end


and intBlock ls st =
   blockPass ls st
   
and 
   intPrint exp st =
      let val (v, newSt) = intExpression exp st
      in
         (printEnv newSt; print (printExpr v); newSt)
      end

and 
   intExpression (EXP_BINARY n) st = intBinary (EXP_BINARY n) st
 | intExpression (EXP_UNARY n) st = intUnary (EXP_UNARY n) st
 | intExpression (EXP_COND n) st = intCond (EXP_COND n) st
 | intExpression (EXP_ASSIGN n) st = intAssign (EXP_ASSIGN n) st
 | intExpression (EXP_ID n) st = intId (EXP_ID n) st
 | intExpression (EXP_VAR n) st = intVar (EXP_VAR n) st 
 | intExpression (EXP_VARASSIGN n) st = intVarAssign (EXP_VARASSIGN n) st 
 | intExpression (EXP_CALL n) st = intCall (EXP_CALL n) st (envToObj st)
 | intExpression (EXP_FUN n) st = intFun (EXP_FUN n) st
 | intExpression (EXP_ANON n) st = intAnon (EXP_ANON n) st
 | intExpression (EXP_IDS n) st = intIds (EXP_IDS n) st
 | intExpression (EXP_OBJECT {props=n}) st = intObject n st
 | intExpression n st = (n, st)

and intObject n st = 
   let val newObj = newTable () 
       val (newObj1, st1) = addObjectProps n newObj st in
         (EXP_ACTUALOBJECT {st=newObj1}, st1)
   end

and addObjectProps (h::t) newObj st = 
      let val (newObj1, st1) = addObjectProp h newObj st in
        addObjectProps t newObj1 st1
      end 
  | addObjectProps [] newObj st = (newObj, st)

and addObjectProp (EXP_OBJECTASSIGN {lft=(EXP_ID lft), rht=rht}) newObj st = 
   let val (rht2, st2) = intExpression rht st in
      (insert newObj (lft, rht2); (newObj, st2))
   end

and 
   intIds (EXP_IDS {expr=n, ids=[]}) st =
      intExpression n st
 | intIds (EXP_IDS {expr=n, ids=ids}) st = 
      let val (id, st1) = (n, st) in 
         case id of 
            EXP_ID stringId =>
               (getVar stringId ids st1, st1)
          | EXP_THIS =>
               (getVar "this" ids st1, st1)
          | _ => error ("bad id: " ^ (printExpr id) ^ " /// " ^ (printExpr n) ^ "\n")
      end

and idToString ((EXP_ID n) :: t) = n :: (idToString t)
  | idToString [] = []

and intVar (EXP_VAR {id=(EXP_ID id)}) st = 
   (EXP_NONE, st) 

and intVarAssign (EXP_VARASSIGN {id=id, assign=assign}) st = 
     intAssign (EXP_ASSIGN {lft=(EXP_IDS {expr=id, ids=[]}),rht=assign}) st 

and getFunction mem st = 
   let val (ast1, st1) = intExpression mem st in
      case ast1 of 
         EXP_CLOSURE {body=body, parms=parms, env=env, r=r} => 
            (ast1, st1, newEnvironment env)
       | EXP_NAMEDCLOSURE {id=(EXP_ID id), clos=(EXP_CLOSURE {body=body, parms=parms, env=env, r=r})} => 
            let val env1 = newEnvironment env 
                val clos = EXP_CLOSURE {body=body, parms=parms, env=env, r=r}
            in
               (insert (getState env1) (id, ast1);
               (clos, st1, env1))
            end
       | _ => error ("attempt to invoke '" ^ (getType ast1) ^ "' value as a function")
   end

and envToObj (ENV {st=st, prev=prev}) = 
   EXP_ACTUALOBJECT {st=st}

and addThis (ENV {st=st, prev=prev}) obj = 
   (insert st ("this", obj); ENV {st=st, prev=prev}) 

and intCall (EXP_CALL {mem=mem, args=(h::t)}) st this = 
   (case h of 
      EXP_ARG n =>
         let
            val (closure, st1, newst1) = getFunction mem st
            val (st2, newst2) = intArg h closure st1 newst1
            val newst3 = addThis newst2 this
            val ret = intCallBody closure newst3
         in
            intCall (EXP_CALL {mem=ret, args=t}) st2 this
         end
    | EXP_DOTID n => 
         (case mem of
            EXP_ACTUALOBJECT {st=obj} =>
               let val ret = find obj n in
                  (case ret of 
                     SOME ret1 => 
                        intCall (EXP_CALL {mem=ret1, args=t}) st mem
                   | NONE => error "val not found"
                  )
               end
          | _ => error "non object returned by function trying to index"
         )
   )
 | intCall (EXP_CALL {mem=mem, args=[]}) st this =  (mem, st)

and
   intCallBody (EXP_CLOSURE {body=body, parms=parms, env=env, r=r}) st =
      let val (ret1, st1) = intSubProgram body st in
         ret1
      end

and 
   intArg (EXP_ARG (h1::t1)) (EXP_CLOSURE {body=body, parms=(h2::t2), env=env, r=r}) st newst=
      let val (arg, st0) = intExpression h1 st in 
         (insert (getState newst) (h2, arg); 
         intArg (EXP_ARG t1) (EXP_CLOSURE {body=body, parms=t2, env=env, r=r}) st0 newst)
      end
 | intArg (EXP_ARG []) (EXP_CLOSURE {body=body, parms=(h2::t2), env=env, r=r}) st newst=
      (insert (getState newst) (h2, EXP_UNDEFINED); 
       intArg (EXP_ARG []) (EXP_CLOSURE {body=body, parms=t2, env=env, r=r}) st newst)
 | intArg (EXP_ARG (h1::t1)) (EXP_CLOSURE {body=body, parms=[], env=env, r=r}) st newst =
      (st, newst) 
 | intArg (EXP_ARG []) (EXP_CLOSURE {body=body, parms=[], env=env, r=r}) st newst = 
      (st, newst)
 | intArg a b st newst = error ((printExpr a) ^ " " ^ (printExpr b))

and intFun (EXP_FUN {id=id, parms=parms, body=body}) st =
   let val closure = EXP_CLOSURE {body=body, parms=(idToString parms), env=st, r=(getTag())} in
      (EXP_NAMEDCLOSURE {id=id, clos=closure}, st)
   end
   
and intAnon (EXP_ANON {parms=parms, body=body}) st =  
   let val closure = EXP_CLOSURE {body=body, parms=(idToString parms), env=st, r=(getTag())} in
      (closure, st)
   end

and intId (EXP_ID id) st =
   (getVar id [] st, st)

and 
   intAssign (EXP_ASSIGN {lft= (EXP_IDS {expr=(EXP_ID id), ids=ids}), rht=rht}) st = 
      let 
         val (v1, st1) = intExpression rht st
         val st2 = setVar id ids v1 st1
      in
         (v1, st1) (* TODO: this might not work *)
      end
 | intAssign _ _  = 
      error "BAD ASSIGN!"

and intBinary (EXP_BINARY {opr=opr, lft=lft, rht=rht}) st = 
   let 
      val (left, st1) = intExpression lft st
      fun handlePlus () =
         let val (right, st2) = intExpression rht st1 in
            if binStringCheck left right
            then (doStringBinary opr left right, st2)
            else if binNumCheck left right
            then (doNumBinary opr left right, st2)
            else typeError "+" "number * number or string * string"
               ((getType left) ^ " * " ^ (getType right))

         end
      fun handleNum () = 
         let val (right, st2) = intExpression rht st1 in
            if binNumCheck left right
            then (doNumBinary opr left right, st2)
            else typeError (getBinString opr) "number * number"
               ((getType left) ^ " * " ^ (getType right))
         end
      fun handleRel () =
         let val (right, st2) = intExpression rht st1 in
            if binNumCheck left right
            then (doRelBinary opr left right, st2)
            else typeError (getBinString opr) "number * number"
               ((getType left) ^ " * " ^ (getType right))
         end
      fun handleEq () = 
         let val (right, st2) = intExpression rht st1 in 
            if binSameCheck left right
            then (doEqBinary opr left right, st2)
            else case opr of
               BOP_EQ => (EXP_FALSE, st2)
             | BOP_NE => (EXP_TRUE, st2)
         end
      fun handleOr () = 
         if unBoolCheck left
         then case left of
            EXP_TRUE => (EXP_TRUE, st1)
          | EXP_FALSE => 
               let val (right, st2) = intExpression rht st1 in
                  if unBoolCheck right
                  then (right, st2)
                  else typeError "||" "boolean * boolean" 
                     ((getType left) ^ " * " ^ (getType right))
               end
            else typeError "||" "boolean" (getType left)
      fun handleAnd () = 
         if unBoolCheck left
         then case left of
            EXP_TRUE => 
               let val (right, st2) = intExpression rht st1 in 
                  if unBoolCheck right
                  then (right, st2)
                  else typeError "&&" "boolean * boolean" 
                     ((getType left) ^ " * " ^ (getType right))
               end
          | EXP_FALSE => (EXP_FALSE, st1)
          else typeError "&&" "boolean" (getType left)
      fun handleComma () = 
         let val (left, st2) = intExpression lft st1
         in
            intExpression rht st1
         end
   in 
      case opr of
         BOP_PLUS => handlePlus ()
       | BOP_MINUS => handleNum ()
       | BOP_TIMES => handleNum ()
       | BOP_DIVIDE => handleNum ()
       | BOP_MOD => handleNum ()
       | BOP_EQ => handleEq ()
       | BOP_NE => handleEq ()
       | BOP_LT => handleRel ()
       | BOP_LE => handleRel ()
       | BOP_GT => handleRel ()
       | BOP_GE => handleRel ()
       | BOP_AND => handleAnd ()
       | BOP_OR => handleOr ()
       | BOP_COMMA => handleComma ()
   end

and intUnary (EXP_UNARY {opr=opr, opnd=opnd}) st = 
   let
      val (ret, st1) = intExpression opnd st 
      fun handleNot () =
         if unBoolCheck ret 
         then (doNot ret, st1)
         else (print "unary "; typeError "!" "boolean" (getType opnd)) 
      fun handleTypeof () =
         (doTypeof ret, st1)
      fun handleMinus () =
         if unNumCheck ret
         then (doMinus ret, st1)
         else (print "unary "; typeError "-" "number" (getType opnd))
   in
      case opr of 
         UOP_NOT => handleNot ()
       | UOP_TYPEOF => handleTypeof ()
       | UOP_MINUS => handleMinus ()
   end

and intCond (EXP_COND {guard=guard, thenExp=thenExp, elseExp=elseExp}) st =
   let val (gd, st1) = intExpression guard st
   in
      if unBoolCheck gd
      then if getBoolVal gd
         then
            intExpression thenExp st
         else
            intExpression elseExp st
      else error ("boolean guard required for 'cond' expression, found " ^ (getType gd))
   end 
;

