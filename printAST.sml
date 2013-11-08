use "parser.sml";


fun 
   binOpToStr BOP_PLUS = " + "
 | binOpToStr BOP_MINUS = " - "
 | binOpToStr BOP_TIMES = " * "
 | binOpToStr BOP_DIVIDE = " / "
 | binOpToStr BOP_MOD = " % "
 | binOpToStr BOP_EQ = " == "
 | binOpToStr BOP_NE = " != "
 | binOpToStr BOP_LT = " < "
 | binOpToStr BOP_GT = " > "
 | binOpToStr BOP_LE = " <= "
 | binOpToStr BOP_GE = " >= "
 | binOpToStr BOP_AND = " && "
 | binOpToStr BOP_OR = " || "
 | binOpToStr BOP_COMMA = ", "
;

fun
   unOpToStr UOP_NOT = "!"
 | unOpToStr UOP_TYPEOF = "typeof "
 | unOpToStr UOP_MINUS = "-"
;

val commaPrec = 1;
val condPrec = 2;
val orPrec = 3;
val andPrec = 4;
val eqPrec = 5;
val relPrec = 6;
val addPrec = 7;
val multPrec = 8;
val unaryPrec = 9;

fun 
   binPrec BOP_PLUS = addPrec
 | binPrec BOP_MINUS = addPrec
 | binPrec BOP_TIMES = multPrec
 | binPrec BOP_DIVIDE = multPrec
 | binPrec BOP_MOD = multPrec
 | binPrec BOP_EQ = eqPrec
 | binPrec BOP_NE = eqPrec
 | binPrec BOP_LT = relPrec
 | binPrec BOP_GT = relPrec
 | binPrec BOP_LE = relPrec
 | binPrec BOP_GE = relPrec
 | binPrec BOP_AND = andPrec
 | binPrec BOP_OR = orPrec
 | binPrec BOP_COMMA = commaPrec
;

fun
   unPrec UOP_NOT = unaryPrec
 | unPrec UOP_TYPEOF = unaryPrec
 | unPrec UOP_MINUS = unaryPrec
;

fun printAST (PROGRAM {elems=el}) = 
   print (printProgram el)

and 
   printProgram n = 
      String.concatWith "\n" (List.map printSourceElement n)

and 
   printSourceElement (STMT {stmt=stmt}) = printStatement stmt
 | printSourceElement (FUNC {id=id, parms=parms, body=body}) = printFunction id parms body

and printFunction id parms body = 
   "function " ^ (printExpression id) ^ "(" ^
   String.concatWith ", " (List.map printExpression parms) ^
   ")\n{\n" ^
   String.concatWith "\n" (List.map printSourceElement body) ^
   "\n}"

and 
   printStatement (ST_EXP {exp=exp}) = (printExpression exp) ^ ";"
 | printStatement (ST_BLOCK ls) = printBlock ls
 | printStatement (ST_IF {iff=iff, thn=thn}) = printEmptyIf iff thn
 | printStatement (ST_IFELSE {iff=iff, thn=thn, el}) = printIfElse iff thn el 
 | printStatement (ST_PRINT expr) = (printPrint expr) ^ ";"
 | printStatement (ST_ITER {whil=whil, block=block}) = printIter whil block
 | printStatement (ST_VAR expr) = 
      "var " ^ (String.concatWith ", " (List.map printExpression expr)) ^ ";"
 | printStatement (ST_RETURN) = "return;"
 | printStatement (ST_RETURNVAL expr) = "return " ^ (printExpression expr) ^ ";" 

and 
   printExpression (EXP_NUM n) = Int.toString n
 | printExpression (EXP_STRING n) = "\"" ^ String.toString(n) ^ "\""
 | printExpression EXP_TRUE = "true"
 | printExpression EXP_FALSE = "false"
 | printExpression EXP_UNDEFINED = "undefined"
 | printExpression (EXP_BINARY n) = printBinary n
 | printExpression (EXP_UNARY n) = printUnary n
 | printExpression (EXP_COND n) = printCond n
 | printExpression (EXP_ASSIGN {lft=lft, rht=rht}) = printAssign lft rht
 | printExpression (EXP_ID n) = n
 | printExpression (EXP_VAR {id=id}) = printExpression id
 | printExpression (EXP_VARASSIGN {id=id, assign=assign}) = 
      (printExpression id) ^ " = " ^ (printExpression assign)
 | printExpression (EXP_CALL {mem=mem, args=args}) = 
      (printExpression mem) ^ "(" ^ (String.concatWith " " (List.map printExpression args)) ^ ")"
 | printExpression (EXP_ARG args) =
      String.concatWith ", " (List.map printExpression args)
 | printExpression (EXP_FUN {id=id, parms=parms, body=body}) = 
   "function " ^ (printExpression id) ^ "(" ^
   String.concatWith ", " (List.map printExpression parms) ^
   ")\n{\n" ^
   String.concatWith "\n" (List.map printSourceElement body) ^
   "\n}"
 | printExpression (EXP_ANON {parms=parms, body=body}) = 
   "(function (" ^
   String.concatWith ", " (List.map printExpression parms) ^
   ")\n{\n" ^
   String.concatWith "\n" (List.map printSourceElement body) ^
   "\n}\n)"

and printAssign lft rht = 
   "(" ^ (printExpression lft) ^ " = " ^ (printExpression rht) ^ ")"

and appendln (x,y) = 
   x ^ "\n" ^ y

and printBlock ls =
   "{\n" ^ (foldr appendln "" (List.map printSourceElement ls)) ^ "}"

and printIf iff thn = 
   "if (" ^ (printExpression iff) ^ ")\n" ^ (printStatement thn)

and printEmptyIf iff thn = 
   (printIf iff thn) ^ "\nelse\n{\n}"

and printIfElse iff thn el =
   (printIf iff thn) ^ "\nelse\n" ^ (printStatement el)

and printPrint expr = 
   "print " ^ (printExpression expr)

and printIter whil block =
   "while (" ^ (printExpression whil) ^ ")\n" ^ (printStatement block)

and printBinary {opr=opr, lft=lft, rht=rht} =
   let 
      val ret =  (printExpression lft) ^ (binOpToStr opr) 
         ^ (printExpression rht)
   in
      "(" ^ ret ^ ")"
   end

and printUnary {opr=opr, opnd=opnd} = 
   let 
      val ret = (unOpToStr opr) ^ (printExpression opnd)
   in
      "(" ^ ret ^ ")"
   end

and printCond {guard=guard, thenExp=thenExp, elseExp=elseExp} = 
   let 
      val ret = (printExpression guard) ^  " ? " ^ (printExpression thenExp) 
         ^ " : " ^ (printExpression elseExp) 
   in
      "(" ^ ret ^ ")"
   end
;
