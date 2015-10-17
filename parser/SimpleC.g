grammar SimpleC;

program: globals+=varDecl* procedures+=procedureDecl*;

varDecl: 'int' ident=varIdentifier ';';

procedureDecl: 'int' name=ID '(' (formals+=formalParam (',' formals+=formalParam)*)? ')' (contract+=prepost (',' contract+=prepost)*)? '{' stmts+=stmt* 'return' returnExpr=expr ';' '}';

formalParam: 'int' ident=varIdentifier;

prepost: requires | ensures | candidateRequires | candidateEnsures;

requires: 'requires' condition=expr;

ensures: 'ensures' condition=expr;

candidateRequires: 'candidate_requires' condition=expr;

candidateEnsures: 'candidate_ensures' condition=expr;

stmt: varDecl | assignStmt | assertStmt | assumeStmt | havocStmt | callStmt | ifStmt | whileStmt | blockStmt;

assignStmt: lhs=varref '=' rhs=expr ';';

assertStmt: 'assert' condition=expr ';';

assumeStmt: 'assume' condition=expr ';';

havocStmt: 'havoc' var=varref ';';

callStmt: lhs=varref '=' callee=ID '(' (actuals+=expr (',' actuals+=expr)*)? ')' ';';

ifStmt: 'if' '(' condition=expr ')' thenBlock=blockStmt ('else' elseBlock=blockStmt)?;

whileStmt: 'while' '(' condition=expr ')' (invariantAnnotations+=loopInvariant (',' invariantAnnotations+=loopInvariant)*)? body=blockStmt;

blockStmt: '{' stmts+=stmt* '}';

loopInvariant: invariant | candidateInvariant;

invariant: 'invariant' condition=expr;

candidateInvariant: 'candidate_invariant' condition=expr;

expr: ternExpr;

ternExpr: single=lorExpr | args+=lorExpr ('?' args+=lorExpr ':' args+=lorExpr)+;

lorExpr: single=landExpr | args+=landExpr (ops+='||' args+=landExpr)+;

landExpr: single=borExpr | args+=borExpr (ops+='&&' args+=borExpr)+;

borExpr: single=bxorExpr | args+=bxorExpr (ops+='|' args+=bxorExpr)+;

bxorExpr: single=bandExpr | args+=bandExpr (ops+='^' args+=bandExpr)+;

bandExpr: single=equalityExpr | args+=equalityExpr (ops+='&' args+=equalityExpr)+;

equalityExpr: single=relExpr | args+=relExpr ((ops+='==' | ops+='!=') args+=relExpr)+;

relExpr: single=shiftExpr | args+=shiftExpr ((ops+='<' | ops+='<=' | ops+='>' | ops+='>=') args+=shiftExpr)+;

shiftExpr: single=addExpr | args+=addExpr ((ops+='<<' | ops+='>>') args+=addExpr)+;

addExpr: single=mulExpr | args+=mulExpr ((ops+='+' | ops+='-') args+=mulExpr)+;

mulExpr: single=unaryExpr | args+=unaryExpr ((ops+='*' | ops+='/' | ops+='%') args+=unaryExpr)+;

unaryExpr: single=atomExpr | (ops+='+' | ops+='-' | ops+='!' | ops+='~')+ arg=atomExpr;

atomExpr: numberExpr | varrefExpr | parenExpr | resultExpr | oldExpr;

numberExpr: number=NUMBER;

varrefExpr: var=varref;

parenExpr: '(' arg=expr ')';

resultExpr: resultTok='\\result';

oldExpr: oldTok='\\old' '(' arg=varref ')';

varref: ident=varIdentifier;

varIdentifier: name=ID;

ID:   ('a'..'z' | 'A'..'Z' | '_') (DIGIT | 'a'..'z' | 'A'..'Z' | '_')*;

NUMBER  : (DIGIT)+ ;

fragment DIGIT  : '0'..'9';

PLUSPLUS: '++';

MINUSMINUS: '--';

COMMENT: ('//' ~('\n'|'\r')* '\r'? '\n' |   '/*' (.)*? '*/') -> skip;

WS: [\t\r\n\u000C ]+ -> skip;

