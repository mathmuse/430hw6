datatype binaryOperator =
     BOP_PLUS
   | BOP_MINUS
   | BOP_TIMES
   | BOP_DIVIDE
   | BOP_MOD
   | BOP_EQ
   | BOP_NE
   | BOP_LT
   | BOP_GT
   | BOP_LE
   | BOP_GE
   | BOP_AND
   | BOP_OR
   | BOP_COMMA
;

datatype unaryOperator =
     UOP_NOT
   | UOP_TYPEOF
   | UOP_MINUS
;

datatype expression =
     EXP_NUM of int
   | EXP_STRING of string
   | EXP_ID of string
   | EXP_TRUE
   | EXP_FALSE
   | EXP_UNDEFINED
   | EXP_BINARY of {opr: binaryOperator, lft: expression, rht: expression}
   | EXP_UNARY of {opr: unaryOperator, opnd: expression}
   | EXP_COND of {guard: expression, thenExp: expression, elseExp: expression}
   | EXP_ASSIGN of {lft: expression, rht: expression}
   | EXP_VAR of {id: expression}
   | EXP_VARASSIGN of {id: expression, assign: expression}
   | EXP_CALL of {mem: expression, args: expression list}
   | EXP_ARG of expression list
   | EXP_FUN of {id: expression, parms: expression list, body: sourceElement list} 
   | EXP_ANON of {parms: expression list, body: sourceElement list}

and statement =
   ST_EXP of {exp: expression}
 | ST_BLOCK of sourceElement list
 | ST_IF of {iff: expression, thn: statement}
 | ST_IFELSE of {iff: expression, thn: statement, el: statement}
 | ST_PRINT of expression
 | ST_ITER of {whil: expression, block: statement} 
 | ST_VAR of expression list
 | ST_RETURN
 | ST_RETURNVAL of expression

and sourceElement =
   STMT of {stmt: statement}
 | FUNC of {id: expression, parms: expression list, body: sourceElement list} 
;

datatype program =
   PROGRAM of {elems: sourceElement list}
;
