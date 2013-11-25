open TextIO;
use "tokenizer.sml";
use "ast.sml";

fun error s = (output (stdErr, s); OS.Process.exit OS.Process.failure);

val hashFn = HashString.hashString;
val cmpFn = (op =);
exception MissingId;
val initSize = 20;

fun newTable () = 
   mkTable (hashFn, cmpFn) (initSize, MissingId)
;

val tokenMap = [
   (TK_LBRACE, "{"),
   (TK_RBRACE, "}"),
   (TK_LPAREN, "("),
   (TK_RPAREN, ")"),
   (TK_LBRACKET, "["),
   (TK_RBRACKET, "]"),
   (TK_COMMA, ","),
   (TK_SEMI, ";"),
   (TK_QUESTION, "?"),
   (TK_COLON, ":"),
   (TK_DOT, "."),
   (TK_PLUS, "+"),
   (TK_MINUS, "-"),
   (TK_TIMES, "*"),
   (TK_DIVIDE, "/"),
   (TK_MOD, "%"),
   (TK_AND, "&&"),
   (TK_OR, "||"),
   (TK_ASSIGN, "="),
   (TK_EQ, "=="),
   (TK_LT, "<"),
   (TK_LE, "<="),
   (TK_GT, ">"),
   (TK_GE, ">="),
   (TK_NOT, "!"),
   (TK_NE, "!="),
   (TK_ELSE, "else"),
   (TK_FALSE, "false"),
   (TK_FUNCTION, "function"),
   (TK_IF, "if"),
   (TK_NEW, "new"),
   (TK_PRINT, "print"),
   (TK_RETURN, "return"),
   (TK_THIS, "this"),
   (TK_TRUE, "true"),
   (TK_TYPEOF, "typeof"),
   (TK_UNDEFINED, "undefined"),
   (TK_VAR, "var"),
   (TK_WHILE, "while"),
   (TK_EOF, "eof")
];


fun 
   tkToStr (TK_NUM n) = Int.toString(n)
 | tkToStr (TK_ID n) = n
 | tkToStr (TK_STRING n) = n
 | tkToStr n = case pairLookup n tokenMap of
      SOME n => n
    | NONE => error "AHHHH!!!!"
; 

fun exp a b = 
   error ("expected '" ^ a ^ "', found '" ^ (tkToStr b) ^ "'\n")
;

fun
   isExpression TK_NOT = true
 | isExpression TK_TYPEOF = true
 | isExpression TK_MINUS = true
 | isExpression TK_LPAREN = true
 | isExpression (TK_NUM _) = true
 | isExpression TK_TRUE = true
 | isExpression TK_FALSE = true
 | isExpression (TK_STRING _) = true
 | isExpression TK_UNDEFINED = true
 | isExpression (TK_ID _) = true
 | isExpression TK_FUNCTION = true
 | isExpression TK_LBRACE = true
 | isExpression TK_NEW = true
 | isExpression TK_THIS = true
 | isExpression _ = false
;

fun 
   isExpressionStatement TK_LBRACE = false
 | isExpressionStatement n = isExpression n
;

fun isStatement n = 
   if isExpression n 
   then true
   else case n of 
      TK_LBRACE => true
    | TK_IF => true
    | TK_PRINT => true
    | TK_WHILE => true
    | TK_VAR => true
    | TK_FUNCTION => true
    | TK_RETURN => true
    | _ => false
; 

fun
   isFunction TK_FUNCTION = true
 | isFunction _ = false
;

fun
   isBlock TK_LBRACE = true
 | isBlock _ = false
;

fun isIf TK_IF = true
  | isIf _ = false
;

fun isPrint TK_PRINT = true
  | isPrint _ = false;
;

fun isIteration TK_WHILE = true
  | isIteration _ = false
;

fun isVariable TK_VAR = true
  | isVariable _ = false
;

fun isReturn TK_RETURN = true
  | isReturn _ = false
;

fun isEqOp tk = 
   tk = TK_EQ orelse 
   tk = TK_NE
;

fun isRelOp tk = 
   tk = TK_LT orelse
   tk = TK_LE orelse
   tk = TK_GT orelse
   tk = TK_GE
;

fun isAddOp tk = 
   tk = TK_PLUS orelse
   tk = TK_MINUS
;

fun isMultOp tk =
   tk = TK_TIMES orelse
   tk = TK_DIVIDE orelse
   tk = TK_MOD
;

fun isUnaryOp tk = 
   tk = TK_NOT orelse
   tk = TK_TYPEOF orelse
   tk = TK_MINUS
;

fun isAndOp tk = 
   tk = TK_AND
;

fun isOrOp tk = 
   tk = TK_OR
;

fun isCommaOp tk = 
   tk = TK_COMMA
;

fun 
   unTkToOp TK_NOT = UOP_NOT
 | unTkToOp TK_TYPEOF = UOP_TYPEOF
 | unTkToOp TK_MINUS = UOP_MINUS
 | unTkToOp n = error ":("
;

fun 
   binTkToOp TK_PLUS = BOP_PLUS
 | binTkToOp TK_MINUS = BOP_MINUS
 | binTkToOp TK_TIMES = BOP_TIMES
 | binTkToOp TK_DIVIDE = BOP_DIVIDE
 | binTkToOp TK_MOD = BOP_MOD
 | binTkToOp TK_EQ = BOP_EQ
 | binTkToOp TK_NE = BOP_NE
 | binTkToOp TK_LT = BOP_LT
 | binTkToOp TK_GT = BOP_GT
 | binTkToOp TK_LE = BOP_LE
 | binTkToOp TK_GE = BOP_GE
 | binTkToOp TK_AND = BOP_AND
 | binTkToOp TK_OR = BOP_OR
 | binTkToOp TK_COMMA = BOP_COMMA
 | binTkToOp n = error ":(("
;

fun
   isValidId (EXP_ID _) = true
 | isValidId (EXP_IDS {expr=EXP_THIS, ids=_ }) = true
 | isValidId (EXP_IDS {expr=n, ids=_ }) = isValidId n
 | isValidId _ = false
;

fun parseBinary nextFun tkChk fstr tk =  
   let val (tk1, ast) = nextFun fstr tk in 
      if tkChk tk1
      then parseRecBin nextFun tkChk (binTkToOp tk1) fstr (nextToken fstr) ast
      else (tk1, ast)
   end

and parseRecBin nextFun tkChk opr fstr tk lft = 
   let val (tk1, ast) = nextFun fstr tk
       val newast = EXP_BINARY {opr=opr, lft=lft, rht=ast}
   in 
      if tkChk tk1
      then parseRecBin nextFun tkChk (binTkToOp tk1) fstr (nextToken fstr) newast
      else (tk1, newast)
   end
;

fun parse fname =
   let 
      val fstr = TextIO.openIn fname;
      val ast = parseProgram fstr (nextToken fstr)
   in
      PROGRAM {elems = ast}
   end

and parseProgram fstr tk = 
   if isStatement tk
   then 
      let
         val (tk1, ast) = parseSourceElement fstr tk
      in
         ast :: (parseProgram fstr tk1)
      end
   else if tk = TK_EOF
   then []
   else
      exp "eof" tk
      

and parseSourceElement fstr tk =
   if isFunction tk then
      parseFunction fstr tk
   else
      parseStatement fstr tk

and parseFunction fstr tk = 
   if tk = TK_FUNCTION
   then
      let val tk1 = nextToken fstr
      in case tk1 of
         TK_ID id =>
         (let val tk2 = nextToken fstr in
            if tk2 = TK_LPAREN then
               let val (tk3, ast3) = parseParameterList fstr (nextToken fstr) in
               if tk3 = TK_RPAREN then
                  let val tk4 = nextToken fstr in
                  if tk4 = TK_LBRACE then
                     let val (tk5, ast5) = parseFunctionBody fstr (nextToken fstr) in
                        if tk5 = TK_RBRACE then
                           (nextToken fstr, FUNC {id=(EXP_ID id), parms=ast3, body=ast5})
                        else exp "}" tk5
                     end
                  else exp "{" tk4
                  end
               else exp ")" tk3  
               end
            else exp "(" tk2
         end)
       | _ => exp "identifier" tk1

      end      
   else
      exp "function" tk

and parseFunctionBody fstr tk = 
   if isStatement tk
   then 
      let
         val (tk1, ast1) = parseSourceElement fstr tk
         val (tk2, ast2) = parseFunctionBody fstr tk1
      in
         (tk2, (ast1 :: ast2))
      end
   else (tk, [])

and
   parseParameterList fstr (TK_ID n) = 
      let val tk1 = nextToken fstr in
         if tk1 = TK_COMMA then
            let val tk0 = nextToken fstr in
               case tk0 of
                  TK_ID n2 =>
                     let val (tk2, ast2) = parseParameterList fstr tk0 in 
                        (tk2, (EXP_ID n) :: ast2)
                     end
                | _ => exp "identifier" tk0
            end
         else
            (tk1, [EXP_ID n]) 
      end
 | parseParameterList fstr tk = 
      (tk, [])

and parseSubstatement f fstr tk = 
   let val (tk1, ast) = f fstr tk in  
      (tk1, STMT {stmt=ast})
   end

and parseStatement fstr tk =
   if isPrint tk then   
      parseSubstatement parsePrintStatement fstr tk
   else if isExpressionStatement tk then 
      parseSubstatement parseExpressionStatement fstr tk
   else if isBlock tk then
      parseSubstatement parseBlockStatement fstr tk
   else if isIf tk then
      parseSubstatement parseIfStatement fstr tk
   else if isIteration tk then
      parseSubstatement parseIterationStatement fstr tk
   else if isVariable tk then
      parseSubstatement parseVariableStatement fstr tk
   else if isReturn tk then
      parseSubstatement parseReturnStatement fstr tk
   else
      error "bad statement"

and parseVariableStatement fstr tk =
   if tk = TK_VAR then
      let val (tk1, ast1) = parseVariableDeclarationList fstr (nextToken fstr) in
         if tk1 = TK_SEMI then
            (nextToken fstr, ST_VAR ast1)
         else exp ";" tk1
      end
   else exp "var" tk

and parseVariableDeclarationList fstr tk = 
   let val (tk1, ast1) = parseVariableDeclaration fstr tk in
      if tk1 = TK_COMMA then
         let val (tk2, ast2) = parseVariableDeclarationList fstr (nextToken fstr) in
            (tk2, ast1 :: ast2)
         end
      else
         (tk1, [ast1])
   end 


and parseVariableDeclaration fstr (TK_ID n) = 
      let val tk1 = nextToken fstr in
         if tk1 = TK_ASSIGN then
            let val (tk2, ast2) = parseAssignmentExpression fstr (nextToken fstr) in
               (tk2, EXP_VARASSIGN {id=(EXP_ID n), assign=ast2})
            end
         else
            (tk1, EXP_VAR {id=(EXP_ID n)})
      end
  | parseVariableDeclaration fstr tk = exp "identifier" tk

and parseReturnStatement fstr tk =
   if tk = TK_RETURN then
      let val tk1 = nextToken fstr in
         if isExpression tk1 then
            let val (tk2, ast2) = parseExpression fstr tk1 in
               if tk2 = TK_SEMI then
                  (nextToken fstr, ST_RETURNVAL ast2)
               else
                  exp ";" tk2
            end
         else if tk1 = TK_SEMI then
            (nextToken fstr, ST_RETURN)
         else exp ";" tk1
      end
   else
      exp "return" tk

and parseBlockStatement fstr tk =
   if tk = TK_LBRACE
   then
      let val tk0 = nextToken fstr in
         if tk0 = TK_FUNCTION then
            exp "}" tk0
         else
            let val (tk1, ast1) = parseMultipleStatements fstr tk0 in
               if tk1 = TK_RBRACE
               then (nextToken fstr, ST_BLOCK ast1)
               else exp "}" tk1 
            end
      end
   else exp "{" tk

and parseMultipleStatements fstr tk = 
   if isStatement tk
   then 
      let val (tk1, ast1) = parseStatement fstr tk in
         let val (tk2, ast2li) = parseMultipleStatements fstr tk1 in
            (tk2, ast1 :: ast2li)
         end
      end
   else (tk, [])

and parseIfStatement fstr tk = 
   let val tk1 = nextToken fstr in
      if tk1 = TK_LPAREN
      then let val (tk2, ast2) = parseExpression fstr (nextToken fstr) in 
         if tk2 = TK_RPAREN
         then let val (tk3, ast3) = parseBlockStatement fstr (nextToken fstr) in
            if tk3 = TK_ELSE
            then 
               let val (tk4, ast4) = parseBlockStatement fstr (nextToken fstr) in
                  (tk4, ST_IFELSE {iff=ast2, thn=ast3, el=ast4})
               end
            else (tk3, ST_IF {iff=ast2, thn=ast3})
         end
         else exp ")" tk2 
      end
      else exp "(" tk1
   end

and parsePrintStatement fstr tk = 
   let val (tk1, ast1) = parseExpression fstr (nextToken fstr) in
      if tk1 = TK_SEMI
      then (nextToken fstr, ST_PRINT ast1)
      else exp ";" tk1
   end

and parseIterationStatement fstr tk = 
   let val tk0 = nextToken fstr in
      if tk0 = TK_LPAREN 
      then let val (tk1, ast1) = parseExpression fstr (nextToken fstr) in
         if tk1 = TK_RPAREN
         then 
            let val (tk2, ast2) = parseBlockStatement fstr (nextToken fstr) in
               (tk2, ST_ITER {whil=ast1, block=ast2 })
            end
         else exp ")" tk1
      end
      else exp "(" tk0
   end

and parseExpressionStatement fstr tk = 
   let val (tk1, ast1) = parseExpression fstr tk
   in
      if tk1 = TK_SEMI
      then
         (nextToken fstr, ST_EXP {exp=ast1})
      else
         exp ";" tk1
   end


and parseExpression fstr tk = 
   parseBinary parseAssignmentExpression isCommaOp fstr tk

and parseAssignmentExpression fstr tk =
   let val (tk1, ast1) = parseConditionalExpression fstr tk in
      if tk1 = TK_ASSIGN 
      then
         if isValidId ast1 then 
            let val (tk2, ast2) = parseAssignmentExpression fstr (nextToken fstr) in
               (tk2, EXP_ASSIGN {lft=ast1, rht=ast2})
            end
         else
            error "unexpected token '='"
      else
         (tk1, ast1) 
   end

and parseConditionalExpression fstr tk = 
   let val (tk1, ast1) = (parseLogicalORExpression fstr tk) in
      if tk1 = TK_QUESTION
      then
         let val (tk2, ast2) = (parseAssignmentExpression fstr (nextToken fstr)) in
            if tk2 = TK_COLON
            then 
               let val (tk3, ast3) = parseAssignmentExpression fstr (nextToken fstr)
               in
                  (tk3, EXP_COND {guard=ast1, thenExp=ast2, elseExp=ast3})
               end
            else exp ":" tk2 
         end
      else (tk1, ast1)
   end

and parseLogicalORExpression fstr tk =
   parseBinary parseLogicalANDExpression isOrOp fstr tk

and parseLogicalANDExpression fstr tk = 
   parseBinary parseEqualityExpression isAndOp fstr tk

and parseEqualityExpression fstr tk = 
   parseBinary parseRelationalExpression isEqOp fstr tk

and parseRelationalExpression fstr tk = 
   parseBinary parseAdditiveExpression isRelOp fstr tk

and parseAdditiveExpression fstr tk = 
   parseBinary parseMultiplicativeExpression isAddOp fstr tk

and parseMultiplicativeExpression fstr tk = 
   parseBinary parseUnaryExpression isMultOp fstr tk

and parseUnaryExpression fstr tk = 
   if isUnaryOp tk
   then 
      let val tk1 = nextToken fstr
          val (tk2, ast) = parseLeftHandSideExpression fstr tk1
      in
         (tk2, EXP_UNARY {opr = (unTkToOp tk), opnd = ast})
      end
   else parseLeftHandSideExpression fstr tk

and parseLeftHandSideExpression fstr tk = 
   parseCallExpression fstr tk

and parseCallExpression fstr tk = 
   let val (tk1, ast1) = parseMemberExpression fstr tk in 
      if tk1 = TK_LPAREN then
         let val (tk2, ast2) = parseCallArguments fstr tk1 in
            (tk2, EXP_CALL {mem=ast1, args=ast2})
         end
      else
         (tk1, ast1)
   end

and parseCallArguments fstr tk = 
   if tk = TK_LPAREN then 
      let 
         val (tk1, ast1) = parseArguments fstr tk
         val (tk2, ast2) = parseCallArgumentsRec fstr tk1
      in
         (tk2, (ast1 :: ast2)) 
      end
   else
      (tk, [])

and parseCallArgumentsRec fstr tk = 
   if tk = TK_LPAREN then 
      let 
         val (tk1, ast1) = parseArguments fstr tk
         val (tk2, ast2) = parseCallArgumentsRec fstr tk1
      in
         (tk2, (ast1 :: ast2)) 
      end
   else if tk = TK_DOT then
      let 
         val (tk1, ast1) = parseCallId fstr (nextToken fstr)
         val (tk2, ast2) = parseCallArgumentsRec fstr tk1
      in
         (tk2, (ast1 @ ast2)) 
      end
   else
      (tk, [])

and parseCallId fstr tk =
   case tk of 
      TK_ID n => (nextToken fstr, [EXP_DOTID n])
    | n => exp "identifier" n

and parseMemberExpression fstr tk =
      if tk = TK_NEW then
         let val (tk1, ast1) = parseMemberExpression fstr (nextToken fstr)
             val (tk2, ast2) = parseArguments fstr tk1 in 
            let val (tk3, ast3) = parseIds fstr tk2 in
               (tk3, EXP_NEW {expr=ast1, args=ast2, ids=ast3})
            end
         end
      else
         let val (tk1, ast1) = parsePrimaryExpression fstr tk in
            let val (tk2, ast2) = parseIds fstr tk1 in
               (tk2, EXP_IDS {expr=ast1, ids=ast2})
            end
         end

and parseIds fstr tk = 
   if tk = TK_DOT then
      let val tk1 = nextToken fstr in
         case tk1 of 
            TK_ID n => 
               let val (tk1, ast1) = parseIds fstr (nextToken fstr) in
                  (tk1, (EXP_ID n) :: ast1)
               end
          | n => exp  "identifier" n 
      end 
   else
      (tk, [])

and parseArguments fstr tk = 
   if tk = TK_LPAREN then
      let val tk1 = nextToken fstr in
         if tk1 = TK_RPAREN then
            (nextToken fstr, EXP_ARG [])
         else if isExpression tk1 then 
            let val (tk2, ast2) = parseArgumentList fstr tk1 in
               if tk2 = TK_RPAREN then
                  (nextToken fstr, EXP_ARG ast2)
               else 
                  exp ")" tk2
            end
         else 
            exp ")" tk1
      end
   else
      exp "(" tk

and parseArgumentList fstr tk =
   let val (tk1, ast1) = parseAssignmentExpression fstr tk in
      if tk1 = TK_COMMA then
         let val (tk2, ast2) = parseArgumentList fstr (nextToken fstr) in
            (tk2, ast1 :: ast2)
         end
      else 
         (tk1, [ast1])
   end

and parsePrimaryExpression fstr tk =
   case tk of
      TK_LPAREN =>
         let 
            val (tk2, ast) = parseExpression fstr (nextToken fstr)
         in
            if tk2 = TK_RPAREN
            then (nextToken fstr, ast)
            else exp ")" tk2
         end
    | TK_NUM n => (nextToken fstr, EXP_NUM n)
    | TK_TRUE => (nextToken fstr, EXP_TRUE)
    | TK_FALSE => (nextToken fstr, EXP_FALSE)
    | TK_STRING n => (nextToken fstr, EXP_STRING n)
    | TK_UNDEFINED => (nextToken fstr, EXP_UNDEFINED)
    | TK_ID n => (nextToken fstr, EXP_ID n)
    | TK_FUNCTION => parseFunctionExpression fstr tk
    | TK_THIS => (nextToken fstr, EXP_THIS)
    | TK_LBRACE => parseObjectLiteral fstr (nextToken fstr)
    | _ => exp "value" tk

(* already accepted lbrace *)
and parseObjectLiteral fstr tk = 
   case tk of 
      TK_RBRACE => (nextToken fstr, EXP_OBJECT {props=[]})
    | n =>
         let val (tk1, ast1) = parsePropertyList fstr tk in
            (tk1, EXP_OBJECT {props=ast1})
         end

and parsePropertyList fstr tk = 
   let val (tk1, ast1) = parsePropertyAssignment fstr tk in
      if tk1 = TK_COMMA then
         let val (tk2, ast2) = parsePropertyList fstr (nextToken fstr) in 
            (tk2, ast1 :: ast2)
         end
      else if tk1 = TK_RBRACE then
         (nextToken fstr, [ast1]) 
      else 
         exp "}" tk1
   end

and parsePropertyAssignment fstr tk = 
   case tk of 
      TK_ID n => 
         let val tk0 = nextToken fstr in 
            if tk0 = TK_COLON then
               let val (tk1, ast1) = parseAssignmentExpression fstr (nextToken fstr) in
                  (tk1, EXP_OBJECTASSIGN {lft=(EXP_ID n), rht=(ast1)})
               end
            else
               exp ":" tk0
         end
    | n => exp "}" tk


and parseFunctionExpression fstr tk = 
   if tk = TK_FUNCTION
   then
       case nextToken fstr of
         TK_ID n => parseFunctionExpressionId fstr n
       | TK_LPAREN => parseFunctionExpressionNoId fstr TK_LPAREN
       | n => exp "(" n 
   else
      exp "function" tk
   
and parseFunctionExpressionId fstr id =
   let val tk1 = nextToken fstr in
      if tk1 = TK_LPAREN then
           let val (tk3, ast3) = parseParameterList fstr (nextToken fstr) in
              if tk3 = TK_RPAREN then
                 let val tk4 = nextToken fstr in
                    if tk4 = TK_LBRACE then
                       let val (tk5, ast5) = parseFunctionBody fstr (nextToken fstr) in
                          if tk5 = TK_RBRACE then
                             (nextToken fstr, EXP_FUN {id=(EXP_ID id), parms=ast3, body=ast5})
                          else exp "}" tk5
                       end
                    else exp "{" tk4
                 end
              else exp ")" tk3  
           end
      else exp "(" tk1
   end

and parseFunctionExpressionNoId fstr tk = 
   let val (tk3, ast3) = parseParameterList fstr (nextToken fstr) in
      if tk3 = TK_RPAREN then
         let val tk4 = nextToken fstr in
            if tk4 = TK_LBRACE then
               let val (tk5, ast5) = parseFunctionBody fstr (nextToken fstr) in
                  if tk5 = TK_RBRACE then
                     (nextToken fstr, EXP_ANON {parms=ast3, body=ast5})
                  else exp "}" tk5
               end
            else exp "{" tk4
         end
      else exp ")" tk3  
   end

;




